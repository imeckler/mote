{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
module SearchNew where

import Data.Maybe
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.PSQueue as P
import Data.List
import Control.Monad.State

type Func      = String
type TransName = String
data Trans     = Trans { from :: [Func], to :: [Func], name :: TransName }
type Move      = (Int, TransName) -- fmap depth
type Program   = [Move]

-- How to make the graph of a program?

-- vertices S_i, T_i for each of the source and target functors
-- vertices are created and destroyed
-- vertex N for each natural transformation

type BraidState = [Func]
type BraidView = (Int, [Func], [Func])

tryRewrite :: Trans -> BraidView -> Maybe (BraidState, Move)
tryRewrite (Trans {from, to, name}) (n, preFs, fs) = case leftFromRight from fs of
  Nothing  -> Nothing
  Just fs' -> Just (reverse preFs ++ fs', (n, name))

braidViews :: BraidState -> [BraidView]
braidViews = go 0 [] where
  go :: Int -> BraidState -> BraidState -> [BraidView]
  go n pre l@(f : fs) = (n, reverse pre, l) : go (n + 1) (f:pre) fs
  go n pre [] = [(n, reverse pre, [])]

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

programsOfLengthAtMost :: [Trans] -> Int -> BraidState -> BraidState -> [Program]
programsOfLengthAtMost ts n start end = evalState (go n start) M.empty where
  go :: Int -> BraidState -> State (M.Map BraidState [Program]) [Program]
  go 0 b = return (if b == end then [[]] else [])
  go n b = do
    memo <- get 
    case M.lookup b memo of
      Just ps -> return ps
      Nothing -> do
        progs <- fmap concat . forM (branchOut ts b) $ \(b', move) -> do
          fmap (map (move :)) $ go (n - 1) b'
        put (M.insert b progs memo)
        return progs

-- In our context, we work with digraphs where some subsets of the edges
-- are detached at one of their terminals. Specifically, there is a set
-- of "incoming" edges which have no source, and "outgoing" edges which
-- have no target. Furthermore both these sets are ordered "left to right"
data Vert 
  = Real Vertex
  | Dummy DummyVertex

type Vertex        = Int
type DummyVertex   = Vertex
data NaturalGraph  = NaturalGraph
  { incomingLabeledDummys :: [(DummyVertex, Func)]
  , incomingSuccs         :: Map DummyVertex Vert
  , outgoingDummys        :: [DummyVertex]
  , outgoingPreds         :: Map DummyVertex Vert

  , digraph  :: Map Vertex (TransName, Map Vertex Func)
  }

-- = M.Map Int 

compose :: NaturalGraph -> NaturalGraph -> NaturalGraph
compose ng1 ng2 =
      outgoingDummys' = outgoingDummys
      (g, outgoingPreds', incomingSuccs') =
        foldl _ (M.union g1 g2, outgoingPreds ng1, incomingSuccs ng2)
          (zip (outgoingDummys ng1) (incomingDummys ng2))
--      g         = foldl upd (M.union g1 g2) (zip (outgoing ng1) (incoming ng2))
  NaturalGraph
  { incomingLabeledDummys = incomingLabeledDummys ng1
  , incomingSuccs  = incomingSuccs'
  , outgoingDummys = outgoingDummys'
  , outgoingPreds  = outgoingPreds'
  , digraph        = _
  }
  where
  g1  = digraph g1
  g2  = digraph g2
  g2' = M.map (\(t, adj) -> (t, M.mapKeysMonotonic (+ n1) adj)) $ M.mapKeysMonotonic (+ n1) g2
  n1  = M.size g1

  upd (g, outPreds, inSuccs) (outd, (ind, func)) =
    case (M.lookup outPreds outd, M.lookup inSuccs ind) of
      (Just x, Just y) -> case (x, y) of
        (Real u, Real v)    ->
          let v' = v + n1
          (M.adjust (\(t, adj) -> (t, M.insert v' func adj)) u g , outPreds, inSuccs)

        (Real u, Dummy d)   ->
          (g, M.insert d (Real u) outPreds, inSuccs)
        (Dummy d, Real v)   -> _
        (Dummy d, Dummy d') ->
          ( g
          , M.insert d' (Dummy d) $ M.delete outd outPreds
          , M.insert _ inSuccs)

      _ -> _

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

