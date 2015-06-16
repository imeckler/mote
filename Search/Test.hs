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
import Mote.Search hiding (from, to, name)
import qualified Data.Map as M
import Search.Types.Word (Word(..), InContext(..))
import Search.Graph.ToTerm (fmapped)
import qualified Data.HashMap.Strict as HashMap

import GHC
import Outputable hiding ((<>))
import Data.Function (on)
import Data.Monoid

import Mote.Util
import Type
import Mote.Types
import Mote.ReadType
import Data.Bitraversable
import Data.Bifunctor

import Search.Graph.Types
import qualified Data.HashSet as HashSet

import Data.Time.Clock
import Control.Monad
import Data.Maybe
import Data.Array
import System.Random
import Control.Applicative

funcs = ["[]", "IO", "Maybe", "(,) a"]
types = ["Int", "String", "Bool"]

-- lol this algorithm
bucket = go 1 . List.sort
  where
  res = 0.05
  go _ [] = []
  go i xs =
    let (b, xs') = span (<= i * res) xs
    in b : go (i + 1) xs'


main = do
  Right (funcs', types', tsList) <-
    runWithTestRef $ \r -> runErrorT $ do
      loadFile r "Foo2.hs"
      (,,) <$> mapM renderTyCon funcs <*> mapM renderTyCon types <*> getTransListM

  let tsList'   = filter (\t -> not (mempty == Search.Types.from t || mempty == Search.Types.to t)) tsList
      wordsList = Word <$> map catMaybes (replicateM 4 (Nothing : map Just funcs')) <*> (Nothing : map Just types')
      n         = length wordsList
      words     = listArray (0, n - 1) wordsList
      numPairs  = 1000

  setStdGen (mkStdGen 10)
  randomPairs <- zip <$> replicateM 1000 (randomRIO (0, n - 1)) <*> replicateM 1000 (randomRIO (0, n - 1))
  results <- forM randomPairs $ \(i, j) -> do
    let (src, trg) = (words ! i, words ! j)
        (a, b) = comparison tsList' src trg 4
    print (src, trg, a, b)
    return (a, b)

  print
    . map (\(pre, post) -> fromIntegral post / fromIntegral pre)
    $ filter ((/= 0) . fst) results

  {-do
  Right (_src, _trg, tsList) <- render (Word ["[]"] (Just "Filepath")) (Word ["IO","[]"] (Just "String"))
  let tsList' = filter (\t -> not (mempty == Search.Types.from t || mempty == Search.Types.to t)) tsList
      src = Word [("[]","[]")] (Just ("Foo2.Filepath","[]"))
      trg = Word [("GHC.Types.IO","[]"),("[]","[]")] (Just ("GHC.Base.String","[]"))
  mapM_ print tsList'
  mapM_ (putStrLn . renderAnnotatedTerm . fst)
    . List.sortBy (compare `on` score)
    . map (\g -> (toTerm g, g))
    $ graphsOfSizeAtMost tsList' 5 src trg
    {-
    . map (\g -> (toTerm g, g))
    $ terms -}

  mapM_ print =<< comparison (Word ["[]"] (Just "Filepath")) (Word ["IO","[]"] (Just "Int")) 5
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

getTransListM = do
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
  -- fmap (fmap renderFunc) (readFuncs trg) -- fmap catMaybes $ mapM (fmap (fmap renderSyntacticFunc . extractUnapplied . dropForAlls) . readType) trg
  tsList <- fmap (fmap (bimap renderSyntacticFunc (renderSyntacticFunc . (,[])))) $ transesInScope -- fmap (fmap (fmap renderFunc)) $ transesInScope
  return tsList

renderTyCon tcStr = do
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
  -- fmap (fmap renderFunc) (readFuncs trg) -- fmap catMaybes $ mapM (fmap (fmap renderSyntacticFunc . extractUnapplied . dropForAlls) . readType) trg
  readAndRenderSyntacticFunc tcStr

renderWordM word = do
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
  -- fmap (fmap renderFunc) (readFuncs trg) -- fmap catMaybes $ mapM (fmap (fmap renderSyntacticFunc . extractUnapplied . dropForAlls) . readType) trg
  bitraverse readAndRenderSyntacticFunc readAndRenderSyntacticFunc word



render src trg =
  runWithTestRef $ \r -> runErrorT $ do
    loadFile r "Foo2.hs"
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


comparison tsList src trg n =
  let mss = moveSequencesOfSizeAtMostMemo tsList n src trg
      moveSequenceToTerm = foldr (flip (<>)) mempty . map (\m ->
        case m of
          End pre t -> fmapped (length pre) (name t)
          Middle fs t post -> fmapped (length fs) (name t))
  in
  (length mss, HashSet.size (HashSet.fromList (map moveListToGraph mss)))

{-
  return
    . map (\((t,_),k) -> (renderAnnotatedTerm t, k))
    . List.sortBy (compare `on` (score . fst))
    . map (\(g, k) -> ((toTerm g, g), k))
    . HashMap.toList
    . HashMap.map length $ HashMap.fromListWith (++) (map (\x -> (moveListToGraph x, [x])) mss) -}

      {-  t0 <- getCurrentTime
  x `seq` return ()
  t1 <- getCurrentTime
  return (length x, diffUTCTime t1 t0)

  let programs = moveSequencesOfSizeAtMost tsList n src' trg'
      gs = graphsOfSizeAtMost tsList n src' trg'
  return (length gs) -}
  {-
    ( HashSet.size . HashSet.fromList $ map moveListToGraph programs
    , length programs
    , length gs
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
