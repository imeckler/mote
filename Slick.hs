{-# LANGUAGE LambdaCase,
             OverloadedStrings,
             NamedFieldPuns,
             RecordWildCards #-}
module Main where

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

type Hole = SrcSpan

data SlickState = SlickState
  { holes       :: [Hole]
  , fileData    :: Maybe (FilePath, HsModule RdrName)
  , currentHole :: Maybe Hole
  }

readModule p = fmap (unLoc . parsedSource) $
  parseModule =<< (getModSummary . mkModuleName $ takeBaseName p)

type M = Ghc

ghcInit :: GhcMonad m => m ()
ghcInit = do
  dfs <- getSessionDynFlags
  void . setSessionDynFlags . withFlags [DynFlags.Opt_DeferTypeErrors] $ dfs
    { hscTarget  = HscInterpreted
    , ghcLink    = LinkInMemory
    , ghcMode    = CompManager
    , log_action = \_ _ _ _ _ -> return ()
    }
  where
  withFlags fs dynFs = foldl DynFlags.gopt_set dynFs fs

findEnclosingHole :: (Int, Int) -> [Hole] -> Maybe Hole
findEnclosingHole pos = find (`spans` pos)

loadModuleAt p = do
  -- TODO: Clear old names and stuff
  -- TODO: I think we can actually do all the parsing and stuff ourselves
  -- and then call GHC.loadMoudle to avoid duplicating work
  setTargets . (:[]) =<< guessTarget p Nothing
  load LoadAllTargets
  setContext [IIModule $ mkModuleName (takeBaseName p)]
  readModule p

loadFile :: GhcMonad m => IORef SlickState -> FilePath -> m ()
loadFile stRef p = loadModuleAt p >>= setStateForData stRef p

setStateForData :: GhcMonad m => IORef SlickState -> FilePath -> HsModule RdrName -> m ()
setStateForData stRef p mod = gModifyIORef stRef (\st -> st 
  { fileData    = Just (p, mod)
  , holes       = Holes.holes mod
  , currentHole = Nothing
  })

gReadIORef     = liftIO . readIORef
gModifyIORef x = liftIO . modifyIORef x

loadModuleAndSetupState :: GhcMonad m => IORef SlickState -> FilePath -> m (HsModule RdrName)
loadModuleAndSetupState stRef p = do
  mod <- loadModuleAt p
  mod <$ setStateForData stRef p mod

respond :: IORef SlickState -> FromClient -> M ToClient
respond stRef = \case
  Load p -> Ok <$ loadFile stRef p

  EnterHole (ClientState {..}) -> do
    mod <- gReadIORef stRef >>= \st -> case fileData st of
      Nothing       -> loadModuleAndSetupState stRef path
      Just (p, mod) ->
        if p == path
        then return mod
        else loadModuleAndSetupState stRef path -- maybe shouldn't autoload

    SlickState {holes} <- gReadIORef stRef

    let mh = findEnclosingHole cursorPos holes
    gModifyIORef stRef (\st -> st { currentHole = mh })
    case mh of
      Nothing -> return (Error "No Hole found")
      Just h  -> runErrorT (Holes.setupContext h mod) >>| \case
        Left err -> Error (T.pack err)
        Right () -> Ok

  GetEnv (ClientState {..}) -> do
    fmap currentHole (gReadIORef stRef) >>= \case
      Just h  -> do
        names <-  filter (isNothing . nameModule_maybe) <$> getNamesInScope
        fmap (SetInfoWindow . T.pack . unlines) . forM names $ \name -> do
          x <- showM name
          fmap (\t -> x ++ " :: " ++ t) (showM =<< exprType x)

      Nothing -> return (Error "nohole")

  SendStop -> return Stop

showM :: (GhcMonad m, Outputable a) => a -> m String
showM = showSDocM . ppr

main = do
  stRef <- newIORef (SlickState {holes=[], fileData=Nothing, currentHole=Nothing})
  withFile "/home/izzy/slickserverlog" WriteMode $ \handle -> do
    hSetBuffering handle NoBuffering
    hSetBuffering stdout NoBuffering
    hPutStrLn handle "Testing, testing"
    runGhc (Just libdir) $ do
      ghcInit
      forever $ do
        ln <- liftIO B.getLine
        case decodeStrict ln of
          Nothing  -> do
            return ()
          Just msg -> do
            liftIO $ hPutStrLn handle (show msg)
            resp <- respond stRef msg
            liftIO $ hPutStrLn handle (show resp)
            liftIO $ LB8.putStrLn (encode resp)

{-
test = do
  ghcInit
  loadFile "Foo.hs"
  runStmt "let g = f" RunToCompletion
  showSDocM . ppr =<< exprType "g"
-}
