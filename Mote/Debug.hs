{-# LANGUAGE NamedFieldPuns #-}
module Mote.Debug where

import Mote.Types
import GHC
import           GHC.Paths (libdir)
import Mote.Init
import System.IO
import Mote.Util
import System.FilePath
import System.Directory
import qualified Data.Set as S
import UniqSupply
import DynFlags
import Control.Monad


initialState :: Handle -> IO MoteState
initialState logFile = mkSplitUniqSupply 'x' >>| \uniq -> MoteState
  { fileData = Nothing
  , currentHole = Nothing
  , argHoles = S.empty
  , loadErrors = []
  , logFile
  , uniq
  }

runWithTestRef :: (Ref MoteState -> Ghc b) -> IO b
runWithTestRef x = do
  home <- getHomeDirectory
  withFile (home </> "testlog") WriteMode $ \logFile -> do
    r <- newRef =<< initialState logFile
    run $ do { ghcInit r; x r }

runWithTestRef' x = do
  home <- getHomeDirectory
  withFile (home </> "testlog") WriteMode $ \logFile -> do
    r <- newRef =<< initialState logFile
    run $ do { Mote.Init.initializeWithCabal r; x r }

run :: Ghc a -> IO a
run = runGhc (Just libdir)

ghcInit :: GhcMonad m => Ref MoteState -> m ()
ghcInit _ = do
  dfs <- getSessionDynFlags
  void . setSessionDynFlags . withFlags [DynFlags.Opt_DeferTypeErrors] $ dfs
    { hscTarget  = HscInterpreted
    , ghcLink    = LinkInMemory
    , ghcMode    = CompManager
    , traceLevel = 10
    }
  where
  withFlags fs dynFs = foldl DynFlags.gopt_set dynFs fs

