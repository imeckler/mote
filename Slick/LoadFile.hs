{-# LANGUAGE LambdaCase, NamedFieldPuns, ScopedTypeVariables #-}
module Slick.LoadFile
  ( loadFile
  ) where

import           ErrUtils                (pprErrMsgBag)
import           Exception
import           GHC
import           GhcMonad
import           HscTypes                (srcErrorMessages)
import           Outputable
import           Slick.Holes
import           Slick.Scope
import           Slick.Types
import           Slick.Util

import           Control.Applicative
import           Control.Concurrent.MVar
import           Control.Monad
import           Control.Monad.Trans
import qualified Data.List               as List
import qualified Data.Map                as M
import           System.Directory        (getModificationTime)

loadFile :: Ref SlickState -> FilePath -> M ()
loadFile stRef p = do
  pmod  <- eitherThrow =<< lift handled -- bulk of time is here
  fdata <- getFileDataErr stRef
  let tcmod = typecheckedModule fdata
  his   <- getHoleInfos tcmod
  augmentedHis <- mapM (augment tcmod) his
  gModifyRef stRef (\s -> s {
      fileData = Just (fdata
        { holesInfo = M.fromList $ map (\hi -> (holeSpan $ holeInfo hi, hi)) augmentedHis })
    })
  where
  -- getting suggestions took far too long, so we only compute them if
  -- they're explicitly requested later on
  augment :: TypecheckedModule -> HoleInfo -> M AugmentedHoleInfo
  augment tcmod hi =
    return (AugmentedHoleInfo { holeInfo = hi, suggestions = Nothing })

  -- bulk of time spent here unsurprisingly
  loadModuleAt :: GhcMonad m => FilePath -> m (Either ErrorType ParsedModule)
  loadModuleAt p = do
    -- TODO: I think we can used the parsed and tc'd module that we get
    -- ourselves and then call GHC.loadMoudle to avoid duplicating work
    setTargets . (:[]) =<< guessTarget p Nothing
    load LoadAllTargets >>= \case
      Succeeded ->
        (List.find ((== p) . GHC.ms_hspp_file) <$> GHC.getModuleGraph) >>= \case
          Just m  -> do
            setContext [IIModule . moduleName . ms_mod $ m]
            Right <$> GHC.parseModule m
          Nothing -> error "Could not load module" -- TODO: Throw real error here
      Failed -> 
        Left . GHCError . unlines . reverse . loadErrors <$> gReadRef stRef

  getModules = do
    clearOldHoles
    clearErrors
    _fs <- getSessionDynFlags
    loadModuleAt p >>= \case
      Left err -> return (Left err)
      Right mod -> do
        tcmod <- typecheckModule mod
        setStateForData stRef p tcmod (unLoc $ parsedSource mod)
        gReadRef stRef >>| loadErrors >>| \case
          []   -> Right mod
          errs -> Left . GHCError . ("getModules: " ++) . unlines $ reverse errs

  handled :: Ghc (Either ErrorType ParsedModule)
  handled = do
    fs <- getSessionDynFlags
    ghandle (\(e :: SomeException) -> Left (OtherError $ show e) <$ clearState stRef) $
      handleSourceError (\e ->
        (Left . GHCError . ("handled:" ++) . showErr fs $ srcErrorMessages e) <$ clearState stRef)
        getModules

  clearOldHoles =
    liftIO $ readMVar stRef >>= \s -> case fileData s of
      Nothing                                         -> return ()
      Just (FileData {path, modifyTimeAtLastLoad}) -> do
        t <- getModificationTime path
        when (t /= modifyTimeAtLastLoad) (resetHolesInfo stRef)

  clearErrors = gModifyRef stRef (\s -> s { loadErrors = [] })

  clearState stRef     = gModifyRef stRef (\s -> s {fileData = Nothing, currentHole = Nothing})
  showErr fs           = showSDocForUser fs neverQualify . vcat . pprErrMsgBag
  resetHolesInfo stRef =
    gModifyRef stRef (\s -> s { fileData = fileData s >>| \fd -> fd { holesInfo = M.empty } })

setStateForData :: GhcMonad m => Ref SlickState -> FilePath -> TypecheckedModule -> HsModule RdrName -> m ()
setStateForData stRef path tcmod hsModule = do
  modifyTimeAtLastLoad <- liftIO $ getModificationTime path
  let argHoles = findArgHoles hsModule
  gModifyRef stRef (\st -> st
    { fileData    = Just $
        FileData
        { path
        , hsModule
        , modifyTimeAtLastLoad
        , typecheckedModule=tcmod
        , scopeMap = makeScopeMap hsModule
         -- This emptiness is temporary. It gets filled in at the end of
         -- loadFile. I had to separate this since I painted myself into
         -- a bit of a monadic corner. "augment" (necessary for generating
         -- the holesInfo value, runs in M rather than Ghc.
        , holesInfo = M.empty
        }
    , currentHole = Nothing
    , argHoles
    })
  logS stRef $ "These be the argHoles:" ++ show argHoles

