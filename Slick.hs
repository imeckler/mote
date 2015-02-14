{-# LANGUAGE LambdaCase,
             OverloadedStrings,
             NamedFieldPuns,
             RecordWildCards #-}
module Main where

import DataCon
import TyCon
import Type
--
import SrcLoc
import FastString (fsLit)
import ParseHoleMessage
import qualified Data.Map as M
import Name
import Data.Maybe
import Control.Applicative
import Control.Monad
import Control.Monad.Error
import Protocol
import GhcMonad
import GHC hiding (exprType)
import GHC.Paths
import Data.List (find)
import qualified Holes
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as B8
import qualified Data.ByteString.Lazy as LB
import qualified Data.ByteString.Lazy.Char8 as LB8
import System.FilePath
import Data.IORef
import qualified DynFlags
import Data.Aeson (encode, decodeStrict)
import Outputable
import Util
import qualified Data.Text as T
import System.IO
import Case
import Data.List (isInfixOf)
import qualified Data.List as List
import Types
import UniqSupply (mkSplitUniqSupply)
import ReadType
import Refine
import HscTypes (srcErrorMessages)
import ErrUtils (pprErrMsgBag)

readModule p = fmap (unLoc . parsedSource) $
  GHC.parseModule =<< (getModSummary . mkModuleName $ takeBaseName p)

type M = Ghc

ghcInit :: GhcMonad m => IORef SlickState -> m ()
ghcInit stRef = do
  dfs <- getSessionDynFlags
  void . setSessionDynFlags . withFlags [DynFlags.Opt_DeferTypeErrors] $ dfs
    { hscTarget  = HscInterpreted
    , ghcLink    = LinkInMemory
    , ghcMode    = CompManager
    , log_action = \fs sev span sty msg -> do
        -- Here be hacks
        let s = showSDoc fs (withPprStyle sty msg)
        logS stRef s
        case ParseHoleMessage.parseHoleInfo s of
          Nothing -> return ()
          Just info -> gModifyIORef stRef (\s ->
            s { holesInfo = M.insert span info (holesInfo s) })
    }
  where
  withFlags fs dynFs = foldl DynFlags.gopt_set dynFs fs

-- tcl_lie should contain the CHoleCan's

findEnclosingHole :: (Int, Int) -> [Hole] -> Maybe Hole
findEnclosingHole pos = find (`spans` pos)

-- TODO: access ghci cmomands from inside vim too. e.g., kind

-- TODO: Don't die on parse errors
loadModuleAt p = handleSourceError (return . Left) . fmap Right $ do
  -- TODO: Clear old names and stuff
  -- TODO: I think we can actually do all the parsing and stuff ourselves
  -- and then call GHC.loadMoudle to avoid duplicating work
  setTargets . (:[]) =<< guessTarget p Nothing
  load LoadAllTargets
  setContext [IIModule $ mkModuleName (takeBaseName p)]
  readModule p

loadFile :: GhcMonad m => IORef SlickState -> FilePath -> m (Either String (HsModule RdrName))
loadFile stRef p = do
  resetHolesInfo stRef
  fs <- getSessionDynFlags
  loadModuleAt p >>= \case
    Left err  -> do
      clearState stRef
      return . Left . showErr fs $ srcErrorMessages err
    Right mod -> Right mod <$ setStateForData stRef p mod
  where
  clearState stRef     = gModifyIORef stRef (\s -> s {fileData = Nothing, currentHole = Nothing})
  showErr fs           = showSDocForUser fs neverQualify . vcat . pprErrMsgBag
  resetHolesInfo stRef =
    gModifyIORef stRef (\s -> s { holesInfo = M.empty })

setStateForData :: GhcMonad m => IORef SlickState -> FilePath -> HsModule RdrName -> m ()
setStateForData stRef p mod = gModifyIORef stRef (\st -> st 
  { fileData    = Just (p, mod)
  , currentHole = Nothing
  })

getHoles :: IORef SlickState -> M [Hole]
getHoles = fmap (M.keys . holesInfo) . gReadIORef 

srcLocPos (RealSrcLoc l) = (srcLocLine l, srcLocCol l)

-- need to invalidate fileData on file write if necessary
respond :: IORef SlickState -> FromClient -> M ToClient
respond stRef = \case
  Load p -> fmap (either Error (const Ok)) $ loadFile stRef p

  NextHole (ClientState {path, cursorPos=(line,col)}) ->
    getHoles stRef >>| \holes -> 
      let mh = 
            case dropWhile ((currPosLoc >=) . srcSpanStart) holes of
              [] -> case holes of
                [] -> Nothing
                (h:_) -> Just h
              (h:_) -> Just h
      in
      maybe Ok (SetCursor . srcLocPos . srcSpanStart) mh
    where
    currPosLoc = mkSrcLoc (fsLit path) line col

  -- inefficient
  PrevHole (ClientState {path, cursorPos=(line, col)}) ->
    getHoles stRef >>| \holes -> 
      let mxs = case takeWhile (< currPosSpan) holes of
                [] -> case holes of {[] -> Nothing; _ -> Just holes}
                xs -> Just xs
      in
      maybe Ok (SetCursor . srcLocPos . srcSpanStart . last) mxs
    where
    currPosSpan = srcLocSpan (mkSrcLoc (fsLit path) line col)

  EnterHole (ClientState {..}) -> fmap (either Error id) . runErrorT $ do
    mod <- lift (gReadIORef stRef) >>= \st -> case fileData st of
      Nothing       -> throwEither . lift $ loadFile stRef path
      Just (p, mod) ->
        if p == path
        then return mod
        else throwEither . lift $ loadFile stRef path -- maybe shouldn't autoload

    SlickState {holesInfo} <- gReadIORef stRef

    let mh = findEnclosingHole cursorPos (M.keys holesInfo)
    gModifyIORef stRef (\st -> st { currentHole = mh })
    case mh of
      Nothing -> return (SetInfoWindow "No Hole found")
      Just _  -> return Ok
    where
    throwEither = (>>= either throwError return)

  GetEnv (ClientState {..}) ->
    fmap currentHole (gReadIORef stRef) >>= \case
      Just h  -> do
        names <-  filter (isNothing . nameModule_maybe) <$> getNamesInScope
        (HoleInfo {..}) <- ((M.! h) . holesInfo) <$> gReadIORef stRef
        let goalStr = "Goal: " ++ holeName ++ " :: " ++ holeTypeStr ++ "\n" ++ replicate 40 '-'
            envVarTypes = map (\(x,t) -> x ++ " :: " ++ t) holeEnv

        return (SetInfoWindow $ unlines (goalStr : envVarTypes))

      Nothing -> return (Error "nohole")

  SendStop -> return Stop

  -- Precondition here: Hole has already been entered
  CaseFurther var (ClientState {path, cursorPos=(line,col)}) -> do
    SlickState {..} <- gReadIORef stRef
    let info = do
          (path, mod)        <- maybeThrow "Filedata not found" fileData
          curr               <- maybeThrow "Current hole not found" currentHole
          HoleInfo {holeEnv} <- maybeThrow "Hole info not found" $
            M.lookup curr holesInfo
          (_, tyStr)         <- maybeThrow "Variable not found in env" $
            List.find ((== var) . fst) holeEnv
          return (mod, path, tyStr, curr)
    case info of
      Left err                     -> return (Error err)
      Right (mod, path, tyStr, currHole) ->
        readType tyStr >>= \case
          Nothing -> return (Error "Could not read type for casing")
          Just ty -> 
            expansions var ty currHole mod >>= \case
              Nothing                    -> return (Error "Variable not found")
              Just ((L sp mg, mi), matches) -> do
                fs <- getSessionDynFlags
                let span              = toSpan sp
                    indentLevel       = subtract 1 . snd . fst $ span
                    indentTail (s:ss) = s : map (replicate indentLevel ' ' ++) ss

                    showMatch :: HsMatchContext RdrName -> Match RdrName (LHsExpr RdrName) -> String
                    showMatch ctx = showSDocForUser fs neverQualify . pprMatch ctx

                    showForUser :: Outputable a => a -> String
                    showForUser = showSDocForUser fs neverQualify . ppr
                return $ case mi of
                  Equation (L l name) ->
                    Replace (toSpan sp) path . unlines . indentTail $
                      map (showMatch (FunRhs name False)) matches

                  CaseBranch ->
                    -- TODO shouldn't always unlines. sometimes should be ; and {}
                    Replace (toSpan sp) path . unlines . indentTail $
                      map (showMatch CaseAlt) matches

                  SingleLambda loc ->
                    Error "TODO: SingleLambda"

    where
    maybeThrow s = maybe (throwError s) return
    currPosSpan  = mkSrcLoc (fsLit path) line col
    toSpan (RealSrcSpan rss) =
      (toPos (realSrcSpanStart rss), toPos (realSrcSpanEnd rss))
    toPos rsl = (srcLocLine rsl, srcLocCol rsl)


  -- every message should really send current file name (ClientState) and
  -- check if it matches the currently loaded file
  GetType e -> do
    fs <- getSessionDynFlags
    logS stRef "gonna get type now"
    x <- exprType e >>| either Error (SetInfoWindow . showSDocForUser fs neverQualify . ppr)
    logS stRef "It worked!"
    return x

showM :: (GhcMonad m, Outputable a) => a -> m String
showM = showSDocM . ppr

main =
  withFile "/home/izzy/slickserverlog" WriteMode $ \logFile -> do
    stRef <- newIORef =<< initialState logFile
    hSetBuffering logFile NoBuffering
    hSetBuffering stdout NoBuffering
    hPutStrLn logFile "Testing, testing"
    runGhc (Just libdir) $ do
      ghcInit stRef
      -- Init.init stRef
      logS stRef "init'd"
      forever $ do
        ln <- liftIO B.getLine
        case decodeStrict ln of
          Nothing  ->
            return ()
          Just msg -> do
            liftIO $ hPutStrLn logFile ("Got: " ++ show msg)
            resp <- respond stRef msg
            liftIO $ hPutStrLn logFile ("Giving: " ++ show resp)
            liftIO $ LB8.putStrLn (encode resp)

initialState logFile = mkSplitUniqSupply 'x' >>| \uniq -> SlickState
  { fileData = Nothing
  , currentHole = Nothing
  , holesInfo = M.empty
  , logFile
  , uniq
  }

testStateRef = do
  h <- openFile "testlog" WriteMode
  newIORef =<< initialState h

runWithTestRef x =
  withFile "/home/izzy/prog/slick/testlog" WriteMode $ \logFile -> do
    r <- newIORef =<< initialState logFile
    run $ do { ghcInit r; x r }


run = runGhc (Just libdir)

