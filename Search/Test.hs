{-# LANGUAGE LambdaCase #-}
module Main where

import Control.Monad.Error
import Search.Types
import Search.Graph
import Mote.Types
import TyCon
import TypeRep
import Mote.ReadType
import Control.Applicative
import qualified Data.List as List
import qualified Data.List.Split as List
import System.Environment (getArgs)
import Mote.Debug
import Mote.LoadFile
import Mote.Search
import qualified Data.Map as M

import qualified Data.HashSet as HashSet
import Data.Maybe
import Debug.Trace
import Data.Function (on)

main :: IO ()
main = do
  (filePath:nStr:fromStr:toStr:_) <- getArgs
  let n    = read nStr :: Int
      from = List.splitOn "," fromStr
      to   = List.splitOn "," toStr
  void . runWithTestRef' $ \r -> runErrorT $ do
    loadFile r filePath
    ts <- transesInScope
    liftIO $ print (length ts)
    gs <- search from to n
    liftIO $
      mapM (\(t, g) ->
        print (renderAnnotatedTerm t, lex (t,g)) )
      . List.sortBy (compare `on` lex)
      . map (\g -> (toTerm g, g))
      . map deleteStrayVertices 
      $ gs
  where
  lex (t, g) = (numHoles t, M.size (digraph g), length $ connectedComponents g)

