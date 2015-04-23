{-# LANGUAGE LambdaCase #-}
module Main where

import Control.Monad.Error
import Search.Types
import Search.Graph
import Slick.Types
import TyCon
import TypeRep
import Slick.ReadType
import Control.Applicative
import qualified Data.List as List
import System.Environment (getArgs)
import Slick.Debug
import Slick.LoadFile
import Slick.Search

import qualified Data.HashSet as HashSet
import Data.Maybe (catMaybes)
import Debug.Trace

main :: IO ()
main = do
  (nStr:_) <- getArgs
  let n = read nStr :: Int
  void . runWithTestRef' $ \r -> runErrorT $ do
    loadFile r "Search/Test.hs"
    ts <- transesInScope
    liftIO $ print (length ts)
    gs <- search from to n
    liftIO (mapM_  (putStrLn . renderTerm . toTerm . traceShowId) gs)
  where
  from = ["[]", "Maybe", "IO"]
  to   = ["IO","[]"]

