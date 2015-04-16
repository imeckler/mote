{-# LANGUAGE RecordWildCards, NamedFieldPuns, LambdaCase, ScopedTypeVariables #-}
module Search.Graph where

import Prelude hiding (sequence)
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.PSQueue as P
import Data.List
import Control.Monad.State hiding (sequence)
import Data.Array.MArray
import Data.Array.ST (STArray)
import Control.Monad.ST (ST, runST)
import Search.Types
import qualified Data.List as List
import Control.Arrow (first, second)

import Data.Aeson
import Data.Monoid
import qualified Data.ByteString.Lazy as BL
import qualified Data.Text as T
import Data.Char (ord)

type BraidState f = [f]
type BraidView  f = ([f], [f])

-- In our context, we work with digraphs where some subsets of the edges
-- are detached at one of their terminals. Specifically, there is a set
-- of "incoming" edges which have no source, and "outgoing" edges which
-- have no target. Furthermore both these sets are ordered "left to right"
data Vert 
  = Real Vertex
  | Dummy DummyVertex
  deriving (Show, Eq, Ord)

type Vertex        = Int
type DummyVertex   = Vertex
-- One imagines the incoming dummys are labeled 0 to incomingCount - 1 and
-- the outgoing dummys are labeled 0 to outgoingCount - 1
data NaturalGraph f = NaturalGraph
  { incomingLabels :: [f]
  , incomingSuccs  :: Map DummyVertex Vert
  , incomingCount  :: Int

  , outgoingPreds  :: Map DummyVertex Vert
  , outgoingCount  :: Int

  , digraph        :: Map Vertex (TransName, [(Vert, f)])
  }
  deriving (Show)

-- Transformations to and from the identity functor are not handled
-- properly.
programToNaturalGraph :: Program f -> NaturalGraph f
programToNaturalGraph = foldl1 (\acc g -> sequence acc g) . map moveToNaturalGraph where
  moveToNaturalGraph :: Move f -> NaturalGraph f
  moveToNaturalGraph (ls, t, rs) =
    NaturalGraph
    { incomingLabels = ls ++ from t ++ rs
    , incomingSuccs = M.fromList $
        map (\i -> (i, Dummy i)) [0..(nl - 1)]
        ++ map (\i -> (nl + i, Real 0)) [0..(nt_i - 1)]
        ++ map (\i -> (nl + nt_i + i, Dummy (nl + nt_o + i))) [0..(nr - 1)]

    , incomingCount = nl + nt_i + nr

    , outgoingPreds = M.fromList $
        map (\i -> (i, Dummy i)) [0..(nl -1)]
        ++ map (\i -> (nl + i, Real 0)) [0..(nt_o - 1)]
        ++ map (\i -> (nl + nt_o + i, Dummy (nl + nt_i + i))) [0..(nr - 1)]
    , outgoingCount = nl + nt_o + nr
    , digraph = M.fromList [(0, (name t, zipWith (\i f -> (Dummy (i + nl), f)) [0..] (to t) ))]
    }
    where
    nl   = length ls
    nr   = length rs
    nt_i = length (from t)
    nt_o = length (to t)

idGraph :: [f] -> NaturalGraph f
idGraph fs =
  NaturalGraph
  { incomingLabels = fs
  , incomingSuccs = M.fromList $ map (\i -> (i, Dummy i)) [0..n]
  , incomingCount = n
  , outgoingPreds = M.fromList $ map (\i -> (i, Dummy i)) [0..n]
  , outgoingCount = n
  , digraph = M.empty
  }
  where
  n = length fs

cutProofToNaturalGraph :: CutProof f -> NaturalGraph f
cutProofToNaturalGraph cp0 = case cp0 of
  FMap f cp  -> juxtapose (idGraph [f]) (cutProofToNaturalGraph cp)
  At fs cp   -> juxtapose (cutProofToNaturalGraph cp) (idGraph fs)
  Cut cp cp' -> sequence (cutProofToNaturalGraph cp) (cutProofToNaturalGraph cp')
  Axiom t    -> programToNaturalGraph [([], t, [])]

-- How to make the graph of a cut free proof?

-- vertices S_i, T_i for each of the source and target functors
-- vertices are created and destroyed
-- vertex N for each natural transformation

tryRewrite :: Eq f => Trans f -> BraidView f -> Maybe (BraidState f, Move f)
tryRewrite t@(Trans {from, to, name}) (pre, fs) = case leftFromRight from fs of
  Nothing  -> Nothing
  Just fs' -> Just (pre ++ to ++ fs', (pre, t, fs'))

braidViews :: BraidState f -> [BraidView f]
braidViews = go [] where
  go :: BraidState f -> BraidState f -> [BraidView f]
  go pre l@(f : fs) = (reverse pre, l) : go (f:pre) fs
  go pre [] = [(reverse pre, [])]

-- can go either 
branchOut :: Eq f => [Trans f] -> BraidState f -> [(BraidState f, Move f)]
branchOut ts b = concatMap (\v -> mapMaybe (\t -> tryRewrite t v) ts) (braidViews b)

{-
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
-}
-- TODO: Convert real Haskell programs into lists of moves

-- TODO: Analyze program graphs

programsOfLengthAtMost :: Ord f => [Trans f] -> Int -> BraidState f -> BraidState f -> [Program f]
programsOfLengthAtMost ts n start end = runST $ do
  arr <- newSTArray (0, n) M.empty
  go arr n start
  where 
  newSTArray :: (Int, Int) -> Map k v -> ST s (STArray s Int (Map k v))
  newSTArray = newArray

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

juxtapose :: NaturalGraph f -> NaturalGraph f -> NaturalGraph f
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

isomorphic :: NaturalGraph f -> NaturalGraph f -> Bool
isomorphic ng1 ng2 = 
  | incomingCount ng1 != incomingCount ng1 || outgoingCount ng1 != outgoingCount ng2 

runErrorT . flip execState ([], S.empty)

-- Es importante que no cambia (incomingDummys ng1) o
-- (outgoingDummys ng2)

shiftBy n g =
  M.map (\(t, es) -> (t, map (\(v,f) -> (case v of {Real r -> Real (r + n); _ -> v}, f)) es))
  $ M.mapKeysMonotonic (+ n) g

idName i = "net" ++ show i

naturalGraphToJSON :: NaturalGraph String -> Value
naturalGraphToJSON (NaturalGraph {..}) = 
  object
  [ T.pack "nodes" .= nodes
  , T.pack "edges" .= edges
  ]
  where
  nodeObj id lab col  = object [T.pack "id" .= id, T.pack "label" .= lab , T.pack "color" .= col ]
  edgeObj from to lab =
    object
    [ T.pack "from" .= from
    , T.pack "to" .= to
    , T.pack "label" .= lab
    , T.pack "style" .= "arrow"
    ]
  nodes =
    map (\i -> nodeObj ("in" ++ show i) "" "green") [0..(incomingCount - 1)]
    ++ map (\i -> nodeObj ("out" ++ show i) "" "red") [0..(outgoingCount - 1)]
    ++ map (\(i, (t,_)) -> nodeObj ("real" ++ show i) t "gray") (M.toList digraph)
  edges =
    concatMap (\(v, (_,es)) -> map (\(u,f) ->
      edgeObj ("real" ++ show v)
        (case u of { Real r -> "real" ++ show r; Dummy d -> "out" ++ show d })
        f) es)
      (M.toList digraph)
    ++ map (\(lab, (i, vert)) -> 
        let v = case vert of {Dummy d -> "out" ++ show d; Real r -> "real" ++ show r} in
        edgeObj ("in" ++ show i) v lab)
        (zip incomingLabels $ M.toList incomingSuccs)

naturalGraphToJS id ng = mconcat
  [ "network = new vis.Network("
  , "document.getElementById(" ,  show id , "),"
  , map (toEnum . fromEnum) . BL.unpack $ encode (naturalGraphToJSON ng)
  , ",{});"
  ]

naturalGraphsToHTML ngs =
  let js = unlines $ zipWith naturalGraphToJS (map idName [0..]) ngs
      n = length ngs
  in
  unlines
  [ "<html>"
  , "<head>"
  ,   "<style type='text/css'>"
  ,   ".network { width: 500px; height:500px; }"
  ,   "</style>"
  ,   "<script type='text/javascript' src='vis.min.js'></script>"
  ,   "<script type='text/javascript'>" ++ "function draw(){" ++ js ++ "}" ++ "</script>"
  , "</head>"
  , "<body onload='draw()'>"
  ,   unlines $ map (\i -> "<div class='network' id=" ++ show (idName i) ++ "></div>") [0..(n-1)]
  , "</body>"
  , "</html>"
  ]

-- ng1 -> ng2
sequence :: NaturalGraph f -> NaturalGraph f -> NaturalGraph f
sequence ng1 ng2 =
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
--  M.map (\(t, es) -> (t, map (\(v, f) -> (case v of {Real r -> Real (r+n1); _ -> v}, f)) es)) g2
  n1  = M.size g1

  outPreds1 = outgoingPreds ng1
  inSuccs2  = incomingSuccs ng2

  (digraph', outgoingPreds', incomingSuccs') =
    foldl upd
      ( M.union g1 g2'
      , M.map (\case {Real v -> Real (n1+v); x -> x}) (outgoingPreds ng2)
      , incomingSuccs ng1)
      (zip [0..] (incomingLabels ng2))

  updateSuccsAtDummy i v es
    | ((Dummy j, f) : es') <- es, i == j = ((v, f) : es') 
    | (e : es') <- es                    = e : updateSuccsAtDummy i v es'
    | otherwise                          = []

  upd (g, outPreds, inSuccs) (i, func) =
    case (M.lookup i outPreds1, M.lookup i inSuccs2) of
      (Just x, Just y) -> case (x, y) of
        (Real u, Real v)    ->
          let v' = v + n1 in
          (M.adjust (\(t, es) -> (t, updateSuccsAtDummy i (Real v') es)) u g, outPreds, inSuccs)

        (Real u, Dummy d)   ->
          (M.adjust (second $ updateSuccsAtDummy i (Dummy d)) u g, M.insert d (Real u) outPreds, inSuccs)

        (Dummy d, Real v)   ->
          let v' = v + n1 in
          (g, outPreds, M.insert d (Real v') inSuccs)

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

collect :: [Program f] -> [Program f]
collect p = undefined

leftFromRight :: Eq a => [a] -> [a] -> Maybe [a]
leftFromRight (x : xs) [] = Nothing
leftFromRight (x : xs) (y : ys)
  | x == y    = leftFromRight xs ys
  | otherwise = Nothing
leftFromRight [] ys = Just ys

