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
import GHC
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

-- reportModuleCompilationResult
-- loadModuleAt :: GhcMonad m => FilePath -> Either String (HsModule RdrName)
loadModuleAt p = do -- handleSourceError (return . srcErrorMessages) . fmap Right $ do
  -- TODO: Clear old names and stuff
  -- TODO: I think we can actually do all the parsing and stuff ourselves
  -- and then call GHC.loadMoudle to avoid duplicating work
  setTargets . (:[]) =<< guessTarget p Nothing
  load LoadAllTargets
  setContext [IIModule $ mkModuleName (takeBaseName p)]
  readModule p

loadFile :: GhcMonad m => IORef SlickState -> FilePath -> m ()
loadFile stRef p = do
  resetHolesInfo stRef
  loadModuleAt p >>= setStateForData stRef p
  where
  resetHolesInfo stRef =
    gModifyIORef stRef (\s -> s { holesInfo = M.empty })

setStateForData :: GhcMonad m => IORef SlickState -> FilePath -> HsModule RdrName -> m ()
setStateForData stRef p mod = gModifyIORef stRef (\st -> st 
  { fileData    = Just (p, mod)
  , currentHole = Nothing
  })

loadModuleAndSetupState :: GhcMonad m => IORef SlickState -> FilePath -> m (HsModule RdrName)
loadModuleAndSetupState stRef p = do
  mod <- loadModuleAt p
  mod <$ setStateForData stRef p mod

getHoles :: IORef SlickState -> M [Hole]
getHoles = fmap (M.keys . holesInfo) . gReadIORef 

srcLocPos (RealSrcLoc l) = (srcLocLine l, srcLocCol l)

-- need to invalidate fileData on file write if necessary
respond :: IORef SlickState -> FromClient -> M ToClient
respond stRef = \case
  Load p -> Ok <$ loadFile stRef p

  NextHole (ClientState {path, cursorPos=(line,col)}) ->
    getHoles stRef >>| \holes -> case dropWhile ((currPosLoc >=) . srcSpanStart) holes of
      [] -> Ok
      (h:_) -> SetCursor . srcLocPos $ srcSpanStart h
    where
    currPosLoc = mkSrcLoc (fsLit path) line col

  PrevHole (ClientState {path, cursorPos=(line, col)}) ->
    getHoles stRef >>| \holes -> case takeWhile (< currPosSpan) holes of
      [] -> Ok
      xs -> SetCursor . srcLocPos . srcSpanStart $ last xs
    where
    currPosSpan = srcLocSpan (mkSrcLoc (fsLit path) line col)

  EnterHole (ClientState {..}) -> do
    mod <- gReadIORef stRef >>= \st -> case fileData st of
      Nothing       -> loadModuleAndSetupState stRef path
      Just (p, mod) ->
        if p == path
        then return mod
        else loadModuleAndSetupState stRef path -- maybe shouldn't autoload

    SlickState {holesInfo} <- gReadIORef stRef

    let mh = findEnclosingHole cursorPos (M.keys holesInfo)
    gModifyIORef stRef (\st -> st { currentHole = mh })
    case mh of
      Nothing -> return (SetInfoWindow "No Hole found")
      Just _  -> return Ok

      {-
      Just h  -> runErrorT (Holes.setupContext h mod) >>| \case
        Left err -> Error err
        Right () -> Ok -}

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
          (_, tyStr)         <- maybeThrow "Variable not found" $
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
              Just ((L sp mg, mi), pats) -> do
                fs <- getSessionDynFlags
                let span        = toSpan sp
                    indentLevel = subtract 1 . snd . fst $ span
                    indentTail (s:ss) = s : map (replicate indentLevel ' ' ++) ss
                    showForUser :: Outputable a => a -> String
                    showForUser = showSDocForUser fs neverQualify . ppr
                return $ case mi of
                  Equation (L l name) ->
                    let funName = showForUser name in
                    Replace (toSpan sp) path . unlines . indentTail $
                      map (\p -> funName ++ " " ++ showForUser p) pats
                    "" -- $ showPat mg

                  CaseBranch ->
                    -- TODO shouldn't always unlines. sometimes should be ; and {}
                    Replace (toSpan sp) path . unlines . indentTail $
                      map ((++ " -> _") . showForUser) pats

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
    SetInfoWindow . showSDocForUser fs neverQualify . ppr <$> exprType e

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

