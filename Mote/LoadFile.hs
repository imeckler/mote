{-# LANGUAGE LambdaCase, NamedFieldPuns, ScopedTypeVariables #-}
module Mote.LoadFile
  ( loadFile
  ) where

import           ErrUtils                (pprErrMsgBag)
import           Exception
import           GHC
import           GhcMonad
import           HscTypes                (srcErrorMessages)
import           Outputable
import           Mote.Holes
import           Mote.Scope
import           Mote.Types
import           Mote.Util

import           Control.Applicative
import           Control.Concurrent.MVar
import           Control.Monad
import           Control.Monad.Trans
import qualified Data.List               as List
import qualified Data.Map                as M
import           System.Directory        (getModificationTime)
import Mote.Search.TypePoset
import qualified Scratch
-- TODO: Debug imports
import qualified DynFlags
import qualified Mote.Search.NatTransData as NatTransData
import qualified Mote.Search.ChooseAType as ChooseAType

{-
loadModule' :: [(FilePath, Maybe Phase)] -> Ghc SuccessFlag-- InputT GHCi SuccessFlag
loadModule' files = do
  targets <- mapM (uncurry GHC.guessTarget) files

  _ <- GHC.abandonAll
  GHC.setTargets []
  _ <- GHC.load LoadAllTargets

  GHC.setTargets targets
  GHC.load LoadAllTargets -}


loadFile :: Ref MoteState -> FilePath -> M ()
loadFile stRef p = do
  _pmod <- eitherThrow =<< lift handled -- bulk of time is here
  fdata <- getFileDataErr stRef
  let tcmod = typecheckedModule fdata
  his   <- getHoleInfos stRef tcmod
  let augmentedHis = map augment his
  gModifyRef stRef (\s -> s {
      fileData = Just (fdata
        { holesInfo = M.fromList $ map (\hi -> (holeSpan $ holeInfo hi, hi)) augmentedHis })
    })
  where
  -- getting suggestions took far too long, so we only compute them if
  -- they're explicitly requested later on
  augment :: HoleInfo -> AugmentedHoleInfo
  augment hi =
    AugmentedHoleInfo { holeInfo = hi, suggestions = Nothing }

  -- bulk of time spent here unsurprisingly
  loadModuleAt :: GhcMonad m => FilePath -> m (Either ErrorType ParsedModule)
  loadModuleAt p = do
    -- TODO: I think we can used the parsed and tc'd module that we get
    -- ourselves and then call GHC.loadMoudle to avoid duplicating work

    -- The hack of prepending "*" is due to Simon Marlow.
    -- See http://stackoverflow.com/questions/12790341/haskell-ghc-dynamic-compliation-only-works-on-first-compile
    setTargets . (:[]) =<< guessTarget ("*" ++ p) Nothing
    (load LoadAllTargets) >>= \case
      Succeeded ->
        (List.find ((== p) . GHC.ms_hspp_file) <$> GHC.getModuleGraph) >>= \case
          Just m  -> do
            setContext [IIModule . moduleName . ms_mod $ m]

            Right <$> GHC.parseModule m
          Nothing ->
            error "Could not load module" -- TODO: Throw real error here

      Failed -> do
        Left . GHCError . unlines . reverse . loadErrors <$> gReadRef stRef

  getModules = do
    clearOldHoles
    clearErrors
    dfs <- getSessionDynFlags
    GHC.setProgramDynFlags (DynFlags.gopt_set dfs DynFlags.Opt_DeferTypedHoles)
    loadModuleAt p >>= \case
      Left err -> return (Left err)
      Right mod -> do
        tcmod <- typecheckModule mod
        setStateForData stRef p tcmod (unLoc $ parsedSource mod)
        gReadRef stRef >>| loadErrors >>| \case
          []   -> Right mod
          errs ->
            Left . GHCError . ("getModules: " ++) . unlines $ reverse errs

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

setStateForData :: GhcMonad m => Ref MoteState -> FilePath -> TypecheckedModule -> HsModule RdrName -> m ()
setStateForData stRef path tcmod hsModule = do
  modifyTimeAtLastLoad <- liftIO $ getModificationTime path
  let argHoles = findArgHoles hsModule
  (chooseAType, innerVar) <- Scratch.inScopeChooseATypeAndInnerDummy
  -- dynFlags <- getSessionDynFlags
  -- logS stRef (showPpr dynFlags . map (\nd -> (NatTransData.from nd, NatTransData.to nd, NatTransData.name nd)) . concat $ ChooseAType.allData chooseAType)
  -- let ((minimalElt, _) : _) = Scratch.minimalElements (lookupPoset lookupTable)
  gModifyRef stRef (\st -> st
    { fileData    = Just $
        FileData
        { path
        , hsModule
        , modifyTimeAtLastLoad
        , typecheckedModule=tcmod
        , scopeMap = makeScopeMap hsModule
        , chooseATypeData = (chooseAType, innerVar)
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

