{-# LANGUAGE NamedFieldPuns #-}
module Slick.Debug where

import Slick.Types
import GHC
import           GHC.Paths (libdir)
import Slick.Init
import System.IO
import Slick.Util
import System.FilePath
import System.Directory
import qualified Data.Set as S
import UniqSupply
import DynFlags
import Control.Monad


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
  withFile (home </> "prog/slick/testlog") WriteMode $ \logFile -> do
    r <- newRef =<< initialState logFile
    run $ do { ghcInit r; x r }

runWithTestRef' x = do
  home <- getHomeDirectory
  withFile (home </> "prog/slick/testlog") WriteMode $ \logFile -> do
    r <- newRef =<< initialState logFile
    run $ do { Slick.Init.init r; x r }

run :: Ghc a -> IO a
run = runGhc (Just libdir)

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

