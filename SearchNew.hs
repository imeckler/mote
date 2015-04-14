{-# LANGUAGE RecordWildCards, NamedFieldPuns, LambdaCase #-}
module SearchNew where

import Data.Maybe
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.PSQueue as P
import Data.List
import Control.Monad.State
import Data.Array.MArray
import Data.Array.ST (STArray)
import Control.Monad.ST (ST, runST)

type Func      = String
type TransName = String
data Trans     = Trans { from :: [Func], to :: [Func], name :: TransName }
  deriving (Show)
type Move      = ([Func], Trans, [Func]) -- (fs, t, gs) = fmap_{fs} (t at gs)
type Program   = [Move]

-- In our context, we work with digraphs where some subsets of the edges
-- are detached at one of their terminals. Specifically, there is a set
-- of "incoming" edges which have no source, and "outgoing" edges which
-- have no target. Furthermore both these sets are ordered "left to right"
data Vert 
  = Real Vertex
  | Dummy DummyVertex

type Vertex        = Int
type DummyVertex   = Vertex
-- One imagines the incoming dummys are labeled 0 to incomingCount - 1 and
-- the outgoing dummys are labeled 0 to outgoingCount - 1
data NaturalGraph  = NaturalGraph
--  { incomingLabeledDummys :: [(DummyVertex, Func)]
  { incomingLabels :: [Func]
  , incomingSuccs  :: Map DummyVertex Vert
  , incomingCount  :: Int

  , outgoingPreds  :: Map DummyVertex Vert
  , outgoingCount  :: Int

  , digraph        :: Map Vertex (TransName, Map Vertex Func)
  }

programToNaturalGraph :: Program -> NaturalGraph -- programs are composed in diagrammatic order, hence foldl1
programToNaturalGraph = foldl1 compose . map moveToNaturalGraph where
  moveToNaturalGraph :: Move -> NaturalGraph
  moveToNaturalGraph (ls, t, rs) =
    NaturalGraph
    { incomingLabels = ls ++ from t ++ rs
    , incomingSuccs = M.fromList $
        map (\i -> (i, Dummy i)) [0..(nr - 1)]
        ++ map (\i -> (i, Real 0)) [nr..(nr + nt_i - 1)]
        ++ map (\i -> (i, Dummy i)) [(nr + nt_i)..(nr + nt_i + nl - 1)]

    , incomingCount = nl + nt_i + nr

    , outgoingPreds = M.fromList $
        map (\i -> (i, Dummy i)) [0..(nr -1)]
        ++ map (\i -> (i, Real 0)) [nr..(nr + nt_o - 1)]
        ++ map (\i -> (i, Dummy i)) [(nr + nt_o)..(nr + nt_o + nl - 1)]
    , outgoingCount = nl + nt_o + nr
    , digraph = M.fromList [(0, (name t, M.empty))]
    }
    where
    nl   = length ls
    nr   = length rs
    nt_i = length (from t)
    nt_o = length (to t)

-- How to make the graph of a program?

-- vertices S_i, T_i for each of the source and target functors
-- vertices are created and destroyed
-- vertex N for each natural transformation

type BraidState = [Func]
type BraidView = ([Func], [Func])

tryRewrite :: Trans -> BraidView -> Maybe (BraidState, Move)
tryRewrite t@(Trans {from, to, name}) (pre, fs) = case leftFromRight from fs of
  Nothing  -> Nothing
  Just fs' -> Just (pre ++ to ++ fs', (pre, t, fs))

braidViews :: BraidState -> [BraidView]
braidViews = go [] where
  go :: BraidState -> BraidState -> [BraidView]
  go pre l@(f : fs) = (reverse pre, l) : go (f:pre) fs
  go pre [] = [(reverse pre, [])]

-- can go either 
branchOut :: [Trans] -> BraidState -> [(BraidState, Move)]
branchOut ts b = concatMap (\v -> mapMaybe (\t -> tryRewrite t v) ts) (braidViews b)

transes :: [Trans]
transes =
  [ Trans {from=["List","Maybe"], to=["List"], name="catMaybes"}
  , Trans {from=["List", "List"], to=["List"], name="concat"}
  , Trans {from=["Maybe", "Maybe"], to=["Maybe"], name="join"}
  , Trans {from=["List", "IO"], to=["IO", "List"], name="sequenceA"}
  , Trans {from=["Maybe", "IO"], to=["IO", "Maybe"], name="sequenceA"}
  , Trans {from=["List", "Maybe"], to=["Maybe", "List"], name="sequenceA"}
  , Trans {from=["Maybe", "List"], to=["List", "Maybe"], name="sequenceA"}
  ]

-- TODO: Convert real Haskell programs into lists of moves

-- TODO: Analyze program graphs

programsOfLengthAtMost :: [Trans] -> Int -> BraidState -> BraidState -> [Program]
programsOfLengthAtMost ts n start end = runST $ do
  arr <- newArray (0, n) M.empty
  go arr n start
  where 
  -- "go arr n b" is all programs of length 
  go :: STArray s Int (Map BraidState [Program]) -> Int -> BraidState -> ST s [Program]
  go arr 0 b = return $ if b == end then [[]] else []
  go arr n b = do
    memo <- readArray arr n
    case M.lookup b memo of
      Nothing -> do
        progs <- fmap concat . forM (branchOut ts b) $ \(b', move) -> do
          fmap (map (move :)) (go arr (n - 1) b')
        let progs' = if b == end then [] : progs else progs
        writeArray arr n (M.insert b progs' memo)
        return progs'

      Just ps -> return ps
  
  -- evalState (go n start) M.empty where
  -- go :: Int -> BraidState -> State (M.Map BraidState [Program]) [Program]
{-
  go 0 b = return (if b == end then [[]] else [])
  go n b = do
    memo <- get 
    case M.lookup b memo of
      Just ps -> return ps
      Nothing -> do
        progs <- fmap concat . forM (branchOut ts b) $ \(b', move) -> do
          fmap (map (move :)) $ go (n - 1) b'
        let progs' = if b == end then [] : progs else progs
        put (M.insert b progs' memo)
        return progs -}

juxtapose :: NaturalGraph -> NaturalGraph -> NaturalGraph
juxtapose ng1 ng2 =
  NaturalGraph
  { incomingLabels = incomingLabels ng1 ++ incomingLabels ng2
  , incomingSuccs =
      M.union (incomingSuccs ng1)
        (M.map (\case { Real v -> Real (v + n1); Dummy d -> Dummy (d + outCount1) })
          (M.mapKeysMonotonic (+ inCount1) (incomingSuccs ng2)))
  , incomingCount = inCount1 + incomingCount ng2

  , outgoingPreds =
      M.union (outgoingPreds ng1)
        (M.map (\case { Real v -> Real (v + n1); Dummy d -> Dummy (d + inCount1) })
          (M.mapKeysMonotonic (+ outCount1) (outgoingPreds ng2)))

  , outgoingCount = outgoingCount ng1 + outgoingCount ng2

  , digraph = M.union g1 (shiftBy n1 g2)
  }
  where
  inCount1  = incomingCount ng1
  outCount1 = outgoingCount ng1

  g1 = digraph ng1
  g2 = digraph ng2
  n1 = M.size g1

-- Es importante que no cambia (incomingDummys ng1) o
-- (outgoingDummys ng2)

shiftBy n g = M.map (\(t, adj) -> (t, M.mapKeysMonotonic (+ n) adj)) $ M.mapKeysMonotonic (+ n) g

compose :: NaturalGraph -> NaturalGraph -> NaturalGraph
compose ng1 ng2 =
  NaturalGraph
  { incomingLabels = incomingLabels ng1
  , incomingSuccs  = incomingSuccs'
  , incomingCount  = incomingCount ng1

  , outgoingPreds  = outgoingPreds'
  , outgoingCount  = outgoingCount ng2

  , digraph        = digraph'
  }
  where
  g1  = digraph ng1
  g2  = digraph ng2
  g2' = shiftBy n1 g2
  n1  = M.size g1

  outPreds1 = outgoingPreds ng1
  inSuccs2  = incomingSuccs ng2

  (digraph', incomingSuccs', outgoingPreds') =
    foldl upd (M.union g1 g2', outgoingPreds ng2, incomingSuccs ng1)
      (zip [0..] (incomingLabels ng1))

  upd (g, outPreds, inSuccs) (i, func) =
    case (M.lookup i outPreds1, M.lookup i inSuccs2) of
      (Just x, Just y) -> case (x, y) of
        (Real u, Real v)    ->
          let v' = v + n1 in
          (M.adjust (\(t, adj) -> (t, M.insert v' func adj)) u g, outPreds, inSuccs)

        (Real u, Dummy d)   ->
          (g, M.insert d (Real u) outPreds, inSuccs)

        (Dummy d, Real v)   ->
          (g, outPreds, M.insert d (Real v) inSuccs)

        (Dummy d, Dummy d') ->
          ( g
          , M.insert d' (Dummy d) outPreds
          , M.insert d (Dummy d') inSuccs)

      _ -> (g, outPreds, inSuccs)

-- maybe (Just x) f = fmap f


{-
  g such that
    V(g) = V(g1) + V(g2)
    (u, v) in E(g) iff
      (u,v) in g1 or
      (u, v) are a source-target pair
-}

  

{-
dijkstra
  :: BraidState -> M.Map BraidState (Int, (BraidState, Move))
dijkstra init = 
  let nexts = branchOut transes init 
  in
  go M.empty
    (M.fromList . map (\(v, en) -> (v, (init, en))) $ nexts) -- nexts)
    (P.fromList . map (\(v, _) -> v P.:-> 1) $ nexts)
  where
  maxDist = 8
  tooMuch u = length u > 5
  go
    :: M.Map BraidState (Int, (BraidState, Move))
    -> M.Map BraidState (BraidState, Move)
    -> P.PSQ BraidState Int
    -> M.Map BraidState (Int, (BraidState, Move))
  go visited onDeckPreds onDeckDists =
    case P.minView onDeckDists of
      Just (u P.:-> dist, onDeckDists') ->
        let visited' :: M.Map BraidState (Int, (BraidState, Move))
            visited' = M.insert u (dist, fromJust $ M.lookup u onDeckPreds) visited

            nexts = 
              if dist >= maxDist
              then []
              else if tooMuch u
              then []
              else
                filter (\(v, _) -> not (M.member v visited'))
                $ branchOut transes u

            (onDeckPreds', onDeckDists'') =
              foldl (\(ps, ds) (v, en) ->
                let ds' = P.insertWith min v (dist + 1) ds 
                    ps' =
                      if P.lookup v ds' == Just (dist + 1)
                      then M.insert v (u,en) ps
                      else ps
                in (ps', ds'))
                (onDeckPreds, onDeckDists') nexts
        in
        go visited' onDeckPreds' onDeckDists''
      Nothing             -> visited -- visited

prove :: (BraidState, BraidState) -> String
prove (s,t) = go "id" t where
  d        = dijkstra s
  go :: String -> BraidState -> String
  go acc v =
    case M.lookup v d of
      Just (d, (b', (i, t))) ->
        go ("(" ++ intercalate " . " (replicate i "fmap") ++ ")" ++ t ++ " . " ++ acc) b'
      Nothing                -> acc
-}
collect :: [Program] -> [Program]
collect p = undefined

leftFromRight :: Eq a => [a] -> [a] -> Maybe [a]
leftFromRight (x : xs) [] = Nothing
leftFromRight (x : xs) (y : ys)
  | x == y    = leftFromRight xs ys
  | otherwise = Nothing
leftFromRight [] ys = Just ys

