{-# LANGUAGE LambdaCase #-}
module Repl where

import qualified Data.Map as M
import Control.Monad
import HoleContext
import GHC
import GhcMonad
import Outputable
import GHC.Paths
import Data.IORef
import System.FilePath
import Control.Monad.Except hiding (liftIO)

main = do
  pathRef <- newIORef ""
  holeRef <- newIORef []
  runGhc (Just libdir) $ do
    ghcInit
    forever $ do
      liftIO getLine >>= \case
        'p':' ':s -> do
          liftIO $ writeIORef pathRef s
          loadFile s
          liftIO $ putStrLn "loaded"

        "holes"   -> do
          p <- liftIO $ readIORef pathRef
          mod <- readModule p
          let hs = holes mod
          liftIO (writeIORef holeRef hs)
          liftIO . putStrLn =<< showSDocM (ppr hs)

        'c':s -> do
          let n = read s :: Int
          mod <- readModule =<< liftIO (readIORef pathRef)
          let hs = holes mod
          output =<< (runExceptT . setupHoleContext (hs !! n) $ hsmodDecls mod)
          case hsmodDecls mod of
            L _ (SigD (TypeSig lnames _)) : _ -> output lnames

          return ()

        't':' ':e -> do
          output =<< exprType e

        's':_ -> printScope


