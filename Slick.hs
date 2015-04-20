{-# LANGUAGE LambdaCase, NamedFieldPuns, OverloadedStrings, RecordWildCards,
             ScopedTypeVariables, TupleSections #-}
module Main where

import           Control.Applicative        ((<$), (<$>))
import Control.Concurrent (forkIO)
import           Control.Monad.Error
import           Data.Aeson                 (decodeStrict, encode, (.=))
import qualified Data.Aeson as Aeson
import qualified Data.ByteString            as B
import qualified Data.ByteString.Lazy.Char8 as LB8
import           Control.Concurrent.MVar
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
import           UniqSupply                 (mkSplitUniqSupply)

import           System.Directory           (getHomeDirectory,
                                             getModificationTime)
import           System.Exit (exitWith, ExitCode(..))
import           System.FilePath
import           System.IO

import Slick.Scope
import           Slick.Case
import           Slick.GhcUtil
import           Slick.Holes
import qualified Slick.Init
import           Slick.Protocol
import           Slick.ReadType
import           Slick.Refine
import Slick.Suggest (getAndMemoizeSuggestions)
import           Slick.Types
import           Slick.Util

-- DEBUG
import Data.Time.Clock

ghcInit :: GhcMonad m => Ref SlickState -> m ()
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

getEnclosingHole :: Ref SlickState -> (Int, Int) -> M (Maybe AugmentedHoleInfo)
getEnclosingHole stRef pos =
  M.foldrWithKey (\k hi r -> if k `spans` pos then Just hi else r) Nothing
  . holesInfo
  <$> getFileDataErr stRef
-- TODO: access ghci cmomands from inside vim too. e.g., kind

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
  logTimeSince t0 = liftIO $ do
    t <- getCurrentTime
    logS stRef . show $ diffUTCTime t t0

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
    t0 <- liftIO getCurrentTime
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

srcLocPos :: SrcLoc -> (Int, Int)
srcLocPos (RealSrcLoc l)  = (srcLocLine l, srcLocCol l)
srcLocPos UnhelpfulLoc {} = error "srcLocPos: unhelpful loc"

respond :: Ref SlickState -> FromClient -> Ghc ToClient
respond stRef msg = either (Error . show) id <$> runErrorT (respond' stRef msg)

respond' :: Ref SlickState -> FromClient -> M ToClient
respond' stRef = \case
  Load p -> do
    t0 <- liftIO getCurrentTime
    loadFile stRef p
    liftIO . forkIO $ do
      fmap fileData (gReadRef stRef) >>= \case
        Nothing -> return ()
        Just (FileData {holesInfo}) ->
          return ()
          -- no idea if this is kosher
          -- void . runGhc (Just libdir) $ runErrorT (mapM_ (getAndMemoizeSuggestions stRef) (M.elems holesInfo))
    return Ok

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
    when (p /= path) (loadFile stRef path)

    mh <- getEnclosingHole stRef cursorPos
    gModifyRef stRef (\st -> st { currentHole = mh })
    return $ case mh of
      Nothing -> SetInfoWindow "No Hole found"
      Just _  -> Ok

  GetHoleInfo (ClientState {..}) (HoleInfoOptions{..}) -> do
    ahi@(AugmentedHoleInfo {holeInfo=hi}) <- getCurrentHoleErr stRef
    fs <- lift getSessionDynFlags
    let env = map (\(id,t) -> (occNameToString (getOccName id), showType fs t)) (holeEnv hi)
    case sendOutputAsData of
      True -> do
        suggsJSON <-
          if withSuggestions
          then mkSuggsJSON <$> Slick.Suggest.getAndMemoizeSuggestions stRef ahi
          else return []
        return $
          JSON . Aeson.object $
            [ "environment" .= map (\(x, t) -> Aeson.object ["name" .= x, "type" .= t]) env
            , "goal" .= Aeson.object ["name" .= holeNameString hi, "type" .= showType fs (holeType hi) ]
            ]
            ++ suggsJSON
        where
        mkSuggJSON (n, t) = Aeson.object ["name" .= occNameToString (occName n), "type" .= showType fs t]
        mkSuggsJSON suggs = [ "suggestions" .= map mkSuggJSON suggs ]

      False -> do
        suggsStr <-
          if withSuggestions
          then mkSuggsStr <$> Slick.Suggest.getAndMemoizeSuggestions stRef ahi
          else return ""

        let goalStr = "Goal: " ++ holeNameString hi ++ " :: " ++ showType fs (holeType hi)
                    ++ "\n" ++ replicate 40 '-'
            envStr =
              -- TODO: Wow, this is total for the strangest reason. If env
              -- is empty then maxIdentLength never gets used to pad so
              -- maximum doesn't fail.
              let maxIdentLength = maximum $ map (\(x,_) -> length x) env in
              unlines $ map (\(x, t) ->
                take maxIdentLength (x ++ repeat ' ') ++ " :: " ++ t) env
        return . SetInfoWindow $ unlines [goalStr, envStr, "", suggsStr]
        where
        mkSuggsStr suggs = 
          let heading = "Suggestions:\n" ++ replicate 40 '-' in
          unlines (heading : map (\(n, t) -> (occNameToString . occName) n ++ " :: " ++ showType fs t) suggs)

  Refine exprStr (ClientState {..}) -> do
    hi    <- getCurrentHoleErr stRef
    expr' <- refine stRef exprStr
    fs    <- lift getSessionDynFlags
    return $
      Replace (toSpan . holeSpan $ holeInfo hi) path
        (showSDocForUser fs neverQualify (ppr expr'))


  SendStop -> return Stop 

  -- Precondition here: Hole has already been entered
  CaseFurther var ClientState {} -> do
    SlickState {..} <- gReadRef stRef
    FileData {path, hsModule} <- getFileDataErr stRef
    hi@(HoleInfo {holeEnv})   <- holeInfo <$> getCurrentHoleErr stRef

    (id, ty) <- maybeThrow (NoVariable var) $
      List.find (\(id,_) -> var == occNameToString (getOccName id)) holeEnv

    expansions stRef (occNameToString (getOccName id)) ty (holeSpan hi) hsModule >>= \case
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

  CaseOn exprStr (ClientState {..}) -> do
    expr <- parseExpr exprStr
    -- Should actually have general mechanism for getting the scope at
    -- a point...
    FileData {..} <- getFileDataErr stRef
    ty <- getEnclosingHole stRef cursorPos >>= \case
      Nothing -> hsExprType expr
      Just hi -> inHoleEnv typecheckedModule (holeInfo hi) $ tcRnExprTc expr
    ms <- let (line,col) = cursorPos in matchesForTypeAt stRef ty (mkSrcLoc (fsLit "") line col)
    fs <- lift getSessionDynFlags
    let indent n  = (replicate n ' ' ++)
        showMatch = showSDocForUser fs neverQualify . pprMatch (CaseAlt :: HsMatchContext RdrName)
    return
      . Insert cursorPos path
      . unlines
      $ ("case " ++ exprStr ++ " of") : map (indent 2 . showMatch) ms

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
    stRef <- newRef =<< initialState logFile
    hSetBuffering logFile NoBuffering
    hSetBuffering stdout NoBuffering
    hPutStrLn logFile "Testing, testing"
    runGhc (Just libdir) $ do
      -- ghcInit stRef
      Slick.Init.init stRef >>= \case
        Left err -> liftIO $ do
          LB8.putStrLn (encode (Error err))
          exitWith (ExitFailure 1)
        Right () -> return ()

      logS stRef "init'd"
      forever $ do
        ln <- liftIO B.getLine
        case decodeStrict ln of
          Nothing  ->
            liftIO . LB8.putStrLn . encode $ Error "Could not parse message JSON"
          Just msg -> do
            liftIO $ hPutStrLn logFile ("Got: " ++ show msg)
            resp <- respond stRef msg
            liftIO $ hPutStrLn logFile ("Giving: " ++ show resp)
            liftIO $ LB8.putStrLn (encode resp)

initialState :: Handle -> IO SlickState
initialState logFile = mkSplitUniqSupply 'x' >>| \uniq -> SlickState
  { fileData = Nothing
  , currentHole = Nothing
  , argHoles = S.empty
  , loadErrors = []
  , logFile
  , uniq
  }

runWithTestRef :: (Ref SlickState -> Ghc b) -> IO b
runWithTestRef x = do
  home <- getHomeDirectory
  withFile (home </> "testlog") WriteMode $ \logFile -> do
    r <- newRef =<< initialState logFile
    run $ do { ghcInit r; x r }

runWithTestRef' x = do
  home <- getHomeDirectory
  withFile (home </> "prog/slick/testlog") WriteMode $ \logFile -> do
    r <- newRef =<< initialState logFile
    run $ do { Slick.Init.init r; x r }

run :: Ghc a -> IO a
run = runGhc (Just libdir)

