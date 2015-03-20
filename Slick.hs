{-# LANGUAGE LambdaCase, NamedFieldPuns, OverloadedStrings, RecordWildCards,
             ScopedTypeVariables, TupleSections #-}
module Main where

import           Control.Applicative        ((<$), (<$>))
import           Control.Monad.Error
import           Data.Aeson                 (decodeStrict, encode)
import qualified Data.ByteString            as B
import qualified Data.ByteString.Lazy.Char8 as LB8
import           Data.IORef
import qualified Data.List                  as List
import qualified Data.Map                   as M
import           Data.Maybe                 (isNothing)
import qualified Data.Set                   as S
import qualified DynFlags

import           ErrUtils                   (pprErrMsgBag)
import           Exception
import           FastString                 (fsLit, unpackFS)
import           GHC                        hiding (exprType)
import           GHC.Paths
import           HscTypes                   (srcErrorMessages)
import           Name
import           Outputable
import           System.Directory           (getHomeDirectory,
                                            getModificationTime)
import           System.FilePath
import           System.IO
import           UniqSupply                 (mkSplitUniqSupply)

import           Slick.Case
import           Slick.GhcUtil
import           Slick.Holes
import qualified Slick.Init
import           Slick.Protocol
import           Slick.ReadType
import           Slick.Refine
import           Slick.Types
import           Slick.Util

-- TODO: Need better error messages. For now any load failure gives
-- "Cannot add module MODULENAME to context: not a home module"

ghcInit :: GhcMonad m => IORef SlickState -> m ()
ghcInit stRef = do
  dfs <- getSessionDynFlags
  void . setSessionDynFlags . withFlags [DynFlags.Opt_DeferTypeErrors] $ dfs
    { hscTarget  = HscInterpreted
    , ghcLink    = LinkInMemory
    , ghcMode    = CompManager
    , traceLevel = 10
    }
  where
  withFlags fs dynFs = foldl DynFlags.gopt_set dynFs fs

-- tcl_lie should contain the CHoleCan's

findEnclosingHole :: (Int, Int) -> [Hole] -> Maybe Hole
findEnclosingHole pos = List.find (`spans` pos)

getEnclosingHole :: IORef SlickState -> (Int, Int) -> M (Maybe Hole)
getEnclosingHole stRef pos = findEnclosingHole pos . M.keys . holesInfo <$> gReadIORef stRef

getEnclosingHoleInfo :: IORef SlickState -> (Int, Int) -> M (Maybe HoleInfo)
getEnclosingHoleInfo stRef pos =
  M.foldrWithKey (\k hi r -> if k `spans` pos then Just hi else r) Nothing
  . holesInfo
  <$> gReadIORef stRef
-- TODO: access ghci cmomands from inside vim too. e.g., kind


loadModuleAt :: GhcMonad m => FilePath -> m ParsedModule
loadModuleAt p = do
  -- TODO: Clear old names and stuff
  -- TODO: I think we can actually do all the parsing and stuff ourselves
  -- and then call GHC.loadMoudle to avoid duplicating work
  setTargets . (:[]) =<< guessTarget p Nothing
  load LoadAllTargets
  (List.find ((== p) . GHC.ms_hspp_file) <$> GHC.getModuleGraph) >>= \case
    Just m  -> do
      setContext [IIModule . moduleName . ms_mod $ m]
      GHC.parseModule m

    Nothing -> error "Could not load module" -- TODO: Throw real error here

-- handleSourceError (return . Left) . fmap Right $ do

-- TODO: This is throwing and it's not clear how to catch
-- the error properly
loadFile :: IORef SlickState -> FilePath -> M ParsedModule
loadFile stRef p = do
  pmod  <- eitherThrow =<< lift handled
  fdata <- getFileDataErr stRef
  his   <- getHoleInfos (typecheckedModule fdata)
  gModifyIORef stRef (\s -> s {
      holesInfo = M.fromList $ map (\hi -> (holeSpan hi, hi)) his })
  return pmod
  where
  getModules = do
    clearOldHoles
    clearErrors
    _fs <- getSessionDynFlags
    mod <- loadModuleAt p
    tcmod <- typecheckModule mod
    setStateForData stRef p tcmod (unLoc $ parsedSource mod)

    gReadIORef stRef >>| loadErrors >>| \case
      []   -> Right mod
      errs -> Left . GHCError . unlines $ reverse errs

  handled = do
    fs <- getSessionDynFlags
    ghandle (\(e :: SomeException) -> Left (OtherError $ show e) <$ clearState stRef) $
      handleSourceError (\e ->
        (Left . GHCError . showErr fs $ srcErrorMessages e) <$ clearState stRef)
        getModules

  clearOldHoles =
    liftIO $ readIORef stRef >>= \s -> case fileData s of
      Nothing                                         -> return ()
      Just (FileData {path, modifyTimeAtLastLoad}) -> do
        t <- getModificationTime path
        when (t /= modifyTimeAtLastLoad) (resetHolesInfo stRef)

  clearErrors = gModifyIORef stRef (\s -> s { loadErrors = [] })

  clearState stRef     = gModifyIORef stRef (\s -> s {fileData = Nothing, currentHole = Nothing})
  showErr fs           = showSDocForUser fs neverQualify . vcat . pprErrMsgBag
  resetHolesInfo stRef =
    gModifyIORef stRef (\s -> s { holesInfo = M.empty })

setStateForData :: GhcMonad m => IORef SlickState -> FilePath -> TypecheckedModule -> HsModule RdrName -> m ()
setStateForData stRef path tcmod hsModule = do
  modifyTimeAtLastLoad <- liftIO $ getModificationTime path
  let argHoles = findArgHoles hsModule
  gModifyIORef stRef (\st -> st
    { fileData    = Just $
        FileData
        { path
        , hsModule
        , modifyTimeAtLastLoad
        , typecheckedModule=tcmod
        }
    , currentHole = Nothing
    , argHoles
    })
  logS stRef $ "These be the argHoles:" ++ show argHoles

srcLocPos :: SrcLoc -> (Int, Int)
srcLocPos (RealSrcLoc l)  = (srcLocLine l, srcLocCol l)
srcLocPos UnhelpfulLoc {} = error "srcLocPos: unhelpful loc"

respond :: IORef SlickState -> FromClient -> Ghc ToClient
respond stRef msg = either (Error . show) id <$> runErrorT (respond' stRef msg)

respond' :: IORef SlickState -> FromClient -> M ToClient
respond' stRef = \case
  Load p -> const Ok <$> loadFile stRef p

  NextHole (ClientState {path, cursorPos=(line,col)}) ->
    getHoles stRef >>= \holes ->
      let mh =
            case dropWhile ((currPosLoc >=) . srcSpanStart) holes of
              [] -> case holes of {[] -> Nothing; (h:_) -> Just h }
              (h:_) -> Just h
      in
      maybe (throwError NoHole) (return . SetCursor . srcLocPos . srcSpanStart) mh
    where
    currPosLoc = mkSrcLoc (fsLit path) line col

  -- inefficient
  PrevHole (ClientState {path, cursorPos=(line, col)}) ->
    getHoles stRef >>= \holes ->
      let mxs = case takeWhile (< currPosSpan) holes of
                  [] -> case holes of {[] -> Nothing; _ -> Just holes}
                  xs -> Just xs
      in
      maybe (throwError NoHole) (return . SetCursor . srcLocPos . srcSpanStart . last) mxs
    where
    currPosSpan = srcLocSpan (mkSrcLoc (fsLit path) line col)

  EnterHole (ClientState {..}) -> do
    FileData {path=p} <- getFileDataErr stRef
    -- maybe shouldn't autoload
    when (p /= path) (void $ loadFile stRef path)

    mh <- findEnclosingHole cursorPos . M.keys . holesInfo <$> gReadIORef stRef
    gModifyIORef stRef (\st -> st { currentHole = mh })
    return $ case mh of
      Nothing -> SetInfoWindow "No Hole found"
      Just _  -> Ok

  GetEnv (ClientState {..}) -> do
    hi@(HoleInfo {..}) <- getCurrentHoleInfoErr stRef
    fs <- lift getSessionDynFlags
    let tyStr       = showType fs $ holeType hi
        goalStr     = "Goal: " ++ holeNameString hi ++ " :: " ++ tyStr ++ "\n" ++ replicate 40 '-'
        envVarTypes =
          map (\(id,t) -> occNameToString (getOccName id) ++ " :: " ++ showType fs t)
            holeEnv

    return (SetInfoWindow $ unlines (goalStr : envVarTypes))

  Refine exprStr (ClientState {..}) -> do
    h     <- getCurrentHoleErr stRef
    expr' <- refine stRef exprStr
    fs    <- lift getSessionDynFlags
    return $
      Replace (toSpan h) path
        (showSDocForUser fs neverQualify (ppr expr'))


  SendStop -> return Stop

  -- Precondition here: Hole has already been entered
  CaseFurther var ClientState {} -> do
    SlickState {..} <- gReadIORef stRef
    FileData {path, hsModule} <- getFileDataErr stRef
    hi@(HoleInfo {holeEnv})   <- getCurrentHoleInfoErr stRef

    (id, ty) <- maybeThrow (NoVariable var) $
      List.find (\(id,_) -> var == occNameToString (getOccName id)) holeEnv

    expansions (occNameToString (getOccName id)) ty (holeSpan hi) hsModule >>= \case
      Nothing                        -> return (Error "Variable not found")
      Just ((L sp _mg, mi), matches) -> do
        fs <- lift getSessionDynFlags
        let span              = toSpan sp
            indentLevel       = subtract 1 . snd . fst $ span
            indentTail []     = error "indentTail got []"
            indentTail (s:ss) = s : map (replicate indentLevel ' ' ++) ss

            showMatch :: HsMatchContext RdrName -> Match RdrName (LHsExpr RdrName) -> String
            showMatch ctx = showSDocForUser fs neverQualify . pprMatch ctx
        return $ case mi of
          Equation (L _l name) ->
            Replace (toSpan sp) path . unlines . indentTail $
              map (showMatch (FunRhs name False)) matches

          CaseBranch ->
            -- TODO shouldn't always unlines. sometimes should be ; and {}
            Replace (toSpan sp) path . unlines . indentTail $
              map (showMatch CaseAlt) matches

          SingleLambda _loc ->
            Error "TODO: SingleLambda"

{-
  CaseOn exprStr (ClientState {..}) -> do
    expr <- parseExpr exprStr
    -- Should actually have general mechanism for getting the scope at
    -- a point...
    wrap <- getEnclosingHoleInfo stRef cursorPos >>| \case
      Nothing -> id
      Just hi -> ErrorT . withBindings (holeEnv hi) . runErrorT
    ty <- wrap $ hsExprType expr
    ms <- matchesForType ty
    fs <- lift getSessionDynFlags
    let indent n  = (replicate n ' ' ++)
        showMatch = showSDocForUser fs neverQualify . pprMatch (CaseAlt :: HsMatchContext RdrName)
    return
      . Insert cursorPos path
      . unlines
      $ ("case " ++ exprStr ++ " of") : map (indent 2 . showMatch) ms -}

  -- every message should really send current file name (ClientState) and
  -- check if it matches the currently loaded file
  GetType e -> do
    fs <- lift getSessionDynFlags
    x  <- exprType e
    return . SetInfoWindow . showSDocForUser fs neverQualify $ ppr x

showM :: (GhcMonad m, Outputable a) => a -> m String
showM = showSDocM . ppr

main :: IO ()
main = do
  home <- getHomeDirectory
  withFile (home </> "slickserverlog") WriteMode $ \logFile -> do
    stRef <- newIORef =<< initialState logFile
    hSetBuffering logFile NoBuffering
    hSetBuffering stdout NoBuffering
    hPutStrLn logFile "Testing, testing"
    runGhc (Just libdir) $ do
      -- ghcInit stRef
      Slick.Init.init stRef
      logS stRef "init'd"
      forever $ do
        ln <- liftIO B.getLine
        case decodeStrict ln of
          Nothing  ->
            return ()
          Just msg -> do
            logS stRef ("Got: " ++ show msg)
            resp <- respond stRef msg
            logS stRef ("Giving: " ++ show resp)
            liftIO $ LB8.putStrLn (encode resp)

initialState :: Handle -> IO SlickState
initialState logFile = mkSplitUniqSupply 'x' >>| \uniq -> SlickState
  { fileData = Nothing
  , currentHole = Nothing
  , holesInfo = M.empty
  , argHoles = S.empty
  , loadErrors = []
  , logFile
  , uniq
  }

testStateRef :: IO (IORef SlickState)
testStateRef = do
  h <- openFile "testlog" WriteMode
  newIORef =<< initialState h

runWithTestRef :: (IORef SlickState -> Ghc b) -> IO b
runWithTestRef x = do
  home <- getHomeDirectory
  withFile (home </> "prog/slick/testlog") WriteMode $ \logFile -> do
    r <- newIORef =<< initialState logFile
    run $ do { ghcInit r; x r }

runWithTestRef' x = do
  home <- getHomeDirectory
  withFile (home </> "prog/slick/testlog") WriteMode $ \logFile -> do
    r <- newIORef =<< initialState logFile
    run $ do { Slick.Init.init r; x r }

run :: Ghc a -> IO a
run = runGhc (Just libdir)

