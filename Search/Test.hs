{-# LANGUAGE LambdaCase, TupleSections #-}
module Main where

import Control.Monad.Error
import Search.Types
import Search.Graph
import qualified Data.List as List
import qualified Data.List.Split as List
import System.Environment (getArgs)
import Mote.Debug
import Mote.LoadFile
import Mote.Search hiding (from, to)
import qualified Data.Map as M
import Search.Types.Word (Word(..))
import qualified Data.HashMap.Strict as HashMap

import GHC
import Outputable
import Data.Function (on)

import Mote.Util
import Type
import Mote.Types
import Mote.ReadType
import Data.Bitraversable
import Data.Bifunctor

import Search.Graph.Types
import qualified Data.HashSet as HashSet

main =
  print =<< comparison (Word ["[]"] (Just "Filepath")) (Word ["IO","[]"] (Just "Int")) 5
  {-
  void . runWithTestRef $ \r -> runErrorT $ do
    loadFile r "Foo.hs"
    ts <- transesInScope
    sts <- mapM toStringTrans ts
    let stsmap = HashMap.fromListWith (++) (map (\t -> (from t, [t])) sts)
    liftIO $ mapM_ (\(k,v) -> print (k, length v)) (HashMap.toList stsmap)

    gs <- search (Word ["[]"] (Just "Filepath")) (Word ["IO","[]"] (Just "Int")) 4
    liftIO $
      mapM (\(t, g) ->
        print (renderAnnotatedTerm t, lex (t,g)) )
      . List.sortBy (compare `on` lex)
      . map (\g -> (toTerm g, g))
      $ gs -}

  where
  lex (t, g) = (numHoles t, M.size (digraph g), length $ connectedComponents g)

render src trg =
  runWithTestRef $ \r -> runErrorT $ do
    loadFile r "Foo.hs"
    fs <- lift getSessionDynFlags
    let renderSyntacticFunc :: SyntacticFunc -> (String, String)
        renderSyntacticFunc (tc, args) = (showSDoc fs (ppr tc), showSDoc fs (ppr args)) -- (getKey (getUnique tc), hash args)

        readAndRenderSyntacticFunc =
          join
          . fmap
            ( maybeThrow (OtherError "Could not parse functor for search")
              . fmap renderSyntacticFunc
              . extractUnapplied . dropForAlls)
          . readType
    src'  <- bitraverse readAndRenderSyntacticFunc readAndRenderSyntacticFunc src
    trg'  <- bitraverse readAndRenderSyntacticFunc readAndRenderSyntacticFunc trg
    -- fmap (fmap renderFunc) (readFuncs trg) -- fmap catMaybes $ mapM (fmap (fmap renderSyntacticFunc . extractUnapplied . dropForAlls) . readType) trg
    tsList <- fmap (fmap (bimap renderSyntacticFunc (renderSyntacticFunc . (,[])))) $ transesInScope -- fmap (fmap (fmap renderFunc)) $ transesInScope
    return (src', trg', tsList)


comparison src trg n = do
  Right (src', trg', tsList) <- render src trg
  let ts = HashMap.fromListWith (++) (map (\t -> (from t, [t])) tsList)

  print "done with that business"
  return (length $ graphsOfSizeAtMost tsList n src' trg')
  {-
  let programs = moveSequencesOfSizeAtMost tsList n src' trg'
  return 
    ( HashSet.size . HashSet.fromList $ map moveListToGraph programs
    , length programs
    ) -}

--  (src, trg) = (Word ["[]"] (Just "Filepath"), Word ["IO", "[]"] (Just "Int"))

{-
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
-}
