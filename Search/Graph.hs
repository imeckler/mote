{-# LANGUAGE RecordWildCards, NamedFieldPuns, LambdaCase,
             ScopedTypeVariables, BangPatterns, ViewPatterns,
             TupleSections #-}
module Search.Graph where

import Prelude hiding (sequence)
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Map (Map)
import qualified Data.PSQueue as P
import Data.List
import Control.Monad.State hiding (sequence)
import Control.Monad.Error hiding (sequence)
import Control.Monad.Identity hiding (sequence)
import Data.Array.MArray
import Data.Array.ST (STArray)
import Control.Monad.ST (ST, runST)
import Search.Types
import qualified Data.List as List
import Control.Arrow (first, second)
import Data.Either (isRight)

import Data.Aeson
import Data.Monoid
import qualified Data.ByteString.Lazy as BL
import qualified Data.Text as T
import Data.Char (ord)

import Data.Hashable
import qualified Data.HashSet as HashSet
import qualified Data.HashMap.Strict as HashMap

import Debug.Trace

type BraidState f = [f]
type BraidView  f = ([f], [f])

-- TODO: Perhaps add the ability to filter the results by those which
-- satisfy some test cases.

-- In our context, we work with digraphs where some subsets of the edges
-- are detached at one of their terminals. Specifically, there is a set
-- of "incoming" edges which have no source, and "outgoing" edges which
-- have no target. Furthermore both these sets are ordered "left to right"
data Vert 
  = Real Vertex
  | Dummy DummyVertex
  deriving (Show, Eq, Ord)

-- We occasionally require this representation. Notably in
-- connectedComponents (and we could have used it in
-- isomorphic/hashWithSaltGraph).
data UnambiguousVert
  = UReal Vertex
  | UDummy InOrOut DummyVertex
  deriving (Show, Eq, Ord)

data InOrOut = In | Out
  deriving (Show, Eq, Ord)

type Vertex        = Int
type DummyVertex   = Vertex
data VertexData f = VertexData
  { label    :: TransName
  -- We store both the incoming and the outgoing vertices (in the proper
  -- order!) at every vertex to make traversal and obtaining the bimodal
  -- ordering easier. 
  , incoming :: [(Vert, f)]
  , outgoing :: [(Vert, f)]
  }
  deriving (Show, Eq)
-- One imagines the incoming dummys are labeled 0 to incomingCount - 1 and
-- the outgoing dummys are labeled 0 to outgoingCount - 1
data NaturalGraph f = NaturalGraph
  { incomingLabels :: [f]
  , incomingSuccs  :: Map DummyVertex Vert
  , incomingCount  :: Int

  , outgoingPreds  :: Map DummyVertex Vert
  , outgoingCount  :: Int

  , digraph        :: Map Vertex (VertexData f)
  }
  deriving (Show)

instance Hashable f => Eq (NaturalGraph f) where
  (==) g1 g2 = hashWithSalt 0 g1 == hashWithSalt 0 g2 && hashWithSalt 10 g1 == hashWithSalt 10 g2

instance Hashable f => Hashable (NaturalGraph f) where
  hashWithSalt = hashWithSaltGraph

connectedComponents :: NaturalGraph f -> Int
connectedComponents ng = undefined -- go (S.fromList vs)
  where
  vs = map UReal [0..(M.size (digraph ng) - 1)]
    ++ map (UDummy In) [0..(incomingCount ng - 1)]
    ++ map (UDummy Out) [0..(outgoingCount ng - 1)]


-- Transformations to and from the identity functor are not handled
-- properly.
programToGraph :: Program f -> NaturalGraph f
programToGraph = foldl1 (\acc g -> sequence acc g) . map moveToGraph

moveToGraph :: Move f -> NaturalGraph f
moveToGraph (ls, t, rs) =
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
  , digraph = M.fromList
    [ (0, VertexData
        { label=name t
        , incoming=zipWith (\i f -> (Dummy (i + nl), f)) [0..] (from t)
        , outgoing=zipWith (\i f -> (Dummy (i + nl), f)) [0..] (to t) 
        })
    ]
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
  n = length fs - 1

cutProofToNaturalGraph :: CutProof f -> NaturalGraph f
cutProofToNaturalGraph cp0 = case cp0 of
  FMap f cp  -> juxtapose (idGraph [f]) (cutProofToNaturalGraph cp)
  At fs cp   -> juxtapose (cutProofToNaturalGraph cp) (idGraph fs)
  Cut cp cp' -> sequence (cutProofToNaturalGraph cp) (cutProofToNaturalGraph cp')
  Axiom t    -> programToGraph [([], t, [])]

-- How to make the graph of a cut free proof?

-- vertices S_i, T_i for each of the source and target functors
-- vertices are created and destroyed
-- vertex N for each natural transformation

splittings :: [f] -> [([f],[f])]
splittings = go [] where
  go pre l@(f : fs) = (reverse pre, l) : go (f:pre) fs
  go pre [] = [(reverse pre, [])]

fineViews :: [f] -> [([f], [f], [f])]
fineViews = concatMap (\(pre, post) -> map (\(x,y) -> (pre,x,y)) (splittings post)) . splittings

tryRewrite :: Eq f => Trans f -> BraidView f -> Maybe (BraidState f, Move f)
tryRewrite t@(Trans {from, to, name}) (pre, fs) = case leftFromRight from fs of
  Nothing  -> Nothing
  Just fs' -> Just (pre ++ to ++ fs', (pre, t, fs'))

-- Consider using hash table to jump to possible moves rather than trying all
-- of them. Note that this essentially requires looping over all substrings
-- of the current BraidState. If the BraidState is small compared to the
-- number of Transes (which it likely will be in practice), this should be
-- a win.
{-
branchOut :: Eq f => [Trans f] -> BraidState f -> [(BraidState f, Move f)]
branchOut ts b = concatMap (\v -> mapMaybe (\t -> tryRewrite t v) ts) (braidViews b)
-}
branchOut :: (Eq f, Hashable f) => HashMap.HashMap [f] [Trans f] -> BraidState f -> [(BraidState f, Move f)]
branchOut ts = concatMap possibilities . fineViews where
  possibilities (pre, foc, post) =
    let matches = fromMaybe [] (HashMap.lookup foc ts) in
    map (\t -> (pre ++ to t ++ post, (pre, t, post))) matches
-- concatMap (\v -> mapMaybe (\t -> tryRewrite t v) ts) (braidViews b)

-- TODO: Convert real Haskell programs into lists of moves
-- TODO: Analyze program graphs
graphsOfSizeAtMost :: (Hashable f, Ord f, Show f) => [Trans f] -> Int -> BraidState f -> BraidState f -> [NaturalGraph f]
graphsOfSizeAtMost tsList n start end = HashSet.toList $ runST $ do
  arr <- newSTArray (0, n) M.empty
  go arr n start
  where 
  newSTArray :: (Int, Int) -> Map k v -> ST s (STArray s Int (Map k v))
  newSTArray = newArray

  ts = HashMap.fromListWith (++) (map (\t -> (from t, [t])) tsList)

  go arr 0 b = return $ if b == end then HashSet.singleton (idGraph end) else HashSet.empty
  go arr n b = do
    memo <- readArray arr n
    case M.lookup b memo of
      Nothing -> do
        progs <- fmap HashSet.unions . forM (branchOut ts b) $ \(b', move) ->
          fmap (HashSet.map (sequence (moveToGraph move))) (go arr (n - 1) b')
        let progs' = if b == end then HashSet.insert (idGraph end) progs else progs
        writeArray arr n (M.insert b progs' memo)
        return progs'

      Just ps -> return ps

-- Search with heuristics
graphsOfSizeAtMostH :: (Hashable f, Ord f, Show f) => [Trans f] -> Int -> BraidState f -> BraidState f -> [NaturalGraph f]
graphsOfSizeAtMostH tsList n start end = HashSet.toList $ runST $ do
  arr <- newSTArray (0, n) M.empty
  fmap HashSet.unions . forM (branchOut ts start) $ \(b', move) ->
    let g = moveToGraph move in
    fmap (HashSet.map (sequence g)) (go arr (n - 1) b' move)
  where 
  n0 = n -- TODO: Debug
  newSTArray :: (Int, Int) -> Map k v -> ST s (STArray s Int (Map k v))
  newSTArray = newArray

  ts = HashMap.fromListWith (++) (map (\t -> (from t, [t])) tsList)

  -- TODO: Some work is definitely duplicated.
  -- E.g., I start with AB, which gets rewritten to CB, to BC, to ABC, to
  -- AB, I shouldn't keep going since happens next should have been done up
  -- the call stack (or is about to be done).
  -- For each S, n store programs of length n which map out of S (to T), keyed by T
  go arr 0 b move = return $ if b == end then HashSet.singleton (idGraph end) else HashSet.empty
  go arr n b (pre, t, post) = do
    memo <- readArray arr n
    case M.lookup b memo of
      Nothing ->
        if length b > 5
        then return HashSet.empty
        else do
          readArray arr n
          progs <- fmap HashSet.unions . forM (branchOut ts b) $ \(b', move@(_, t', _)) ->
            if from t == [] && from t' == []
            then return HashSet.empty
            else
              let g = moveToGraph move in
              fmap (HashSet.map (sequence g)) (go arr (n - 1) b' move)

          let progs' = if b == end then HashSet.insert (idGraph end) progs else progs
          writeArray arr n (M.insert b progs' memo)
          return progs'

      Just ps -> return ps

programsOfLengthAtMost :: (Hashable f, Ord f) => [Trans f] -> Int -> BraidState f -> BraidState f -> [Program f]
programsOfLengthAtMost tsList n start end = runST $ do
  arr <- newSTArray (0, n) M.empty
  go arr n start
  where 
  ts = HashMap.fromListWith (++) (map (\t -> (from t, [t])) tsList)

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

findMap :: (a -> Maybe b) -> [a] -> Maybe b
findMap f = foldr (\x r -> case f x of { Just y -> Just y; _ -> r }) Nothing

-- TODO: Remove incomingCount. It's just M.size incomingSuccs

-- There are two cases.
-- 1. There is a "good" vertex which is the succsessor of an incoming
--    dummy. A "good" vertex is one whose only incoming vertices are
--    dummys or orphans.
-- 2. The graph represents the identity.
-- Proof.
-- Fact: Any non-good vertex has a predecessor which is neither an orphan
--       nor a dummy.
-- Assume (1) does not hold.
-- Pick any vertex v0 which is the successor of an incoming dummy.
-- By the fact, v0 has a predecessor v1 which is neither an orphan nor a
-- dummy. v1 has
-- a predecessor v2, and so on. We thus obtain an infinitely regressing
-- chain of vertices (infinite because the graph is acyclic) which is
-- impossible since our graph is finite.

renderTerm :: Term -> String
renderTerm = \case
  Id         -> "id"
  Simple s   -> s
  Compound s -> s

toTerm :: Show f => NaturalGraph f -> Term
toTerm = toTerm' . compressPaths

lastMay :: [a] -> Maybe a
lastMay []     = Nothing
lastMay [x]    = Just x
lastMay (_:xs) = lastMay xs

-- Three cases:
-- There are incoming vertices
-- There are no incoming vertices but there are outgoing vertices
-- There are no 
-- there are no incoming vertices or outgoing vertices.
data TopOrBottom = Top | Bottom deriving (Eq, Show)
toTerm' :: Show f => NaturalGraph f -> Term
toTerm' ng0 = case traceShow ng $ findGoodVertex ng of
  Nothing -> Id
  Just (Top, (n, d0, vGood, vGoodData)) ->
    case toTerm' (ng { incomingSuccs = incomingSuccs', digraph = g'', outgoingPreds = outgoingPreds'' }) of
      Id -> fmapped (n + k) goodProgram
      p  -> fmapped k (p <> fmapped n goodProgram)
    where
    dummiesRemoved = length . filter (\case {(Dummy _,_) -> True; _ -> False}) $ incoming vGoodData
    dummiesCreated = length $ outgoing vGoodData
    dummyShift     = dummiesCreated - dummiesRemoved

    (beforeSuccs, afterSuccs) =
      let (before, y) = M.split d0 (incomingSuccs ng)
          (_, after)  = M.split (d0 + dummiesRemoved - 1) y
      in
      (before, after)

    incomingSuccs' = 
      M.unions
      [ beforeSuccs
      , (\x -> traceShow ("outgoing", x) x). M.fromList $ zipWith (\i (v,_) -> (i, v)) [d0..] (outgoing vGoodData)
      , M.mapKeysMonotonic (\k -> k + dummyShift) afterSuccs
      ]

    -- TODO: Merge this with g'
    outgoingPreds' =
      M.foldWithKey (\d ve preds -> case ve of
        Dummy suc -> M.adjust (\_ -> Dummy (d + dummyShift)) suc preds
        _         -> preds)
      (outgoingPreds ng)
      afterSuccs

    outgoingPreds'' =
      foldl (\m (i, (v, _)) -> case v of
        Dummy dum -> M.adjust (\_ -> Dummy i) dum m
        _          -> m)
        outgoingPreds'
        (zip [d0..] (outgoing vGoodData))

    -- This is incorrect
    {-
    g' =
      M.mapWithKey (\r vd -> vd { incoming = map (first (rename r)) (incoming vd) }) (M.delete vGood g)
      where
      rename rCurr ve = case ve of
        Real r ->
          if r == vGood
          then Dummy (d0 + fromJust (findIndex (== Real rCurr) (map fst . outgoing $ vGoodData)))
          else ve
        Dummy d ->
          if d >= d0 + dummiesRemoved then Dummy (d + dummyShift) else ve
-}


    g' =
      foldl (\digY'all r ->
        M.adjust (\vd -> vd { incoming = map (first shift) (incoming vd) }) r digY'all)
        g
        (List.nub . mapMaybe (\case {Real r -> Just r; _ -> Nothing}) $ M.elems afterSuccs)
      where
      shift ve = case ve of
        Dummy d -> if d >= d0 + dummiesRemoved then Dummy (d + dummyShift) else ve
        _       -> ve

    g'' =
      foldl (\digY'all (i, (v,_)) -> case v of
        Real r -> M.adjust (updateIncomingAtFirst (Real vGood) (Dummy i)) r digY'all 
        _      -> digY'all)
        g'
        (zip [d0..] (outgoing vGoodData))

    goodProgram = makeTopGoodProgram vGoodData

  -- d0 is the leftmost dummy child of vGood
  Just (Bottom, (n, d0, vGood, vGoodData)) ->
    case toTerm (ng { incomingSuccs = incomingSuccs'', digraph = g'', outgoingPreds = outgoingPreds' }) of
      Id -> fmapped (n + k) goodProgram -- I think n will always be 0 in this case
      p  -> fmapped k (fmapped n goodProgram <> p)
    where
    dummiesCreated = length $ incoming vGoodData
    dummiesRemoved = length . filter (\case {(Dummy _,_) -> True; _ -> False}) $ outgoing vGoodData
    dummyShift     = dummiesCreated - dummiesRemoved

    (beforePreds, afterPreds) =
      let (before, y) = M.split d0 (outgoingPreds ng)
          (_, after)  = M.split (d0 + dummiesRemoved - 1) y
      in
      (before, after)

    outgoingPreds' =
      M.unions
      [ beforePreds
      , M.fromList $ zipWith (\i (v,_) -> (i, v)) [d0..] (incoming vGoodData)
      , M.mapKeysMonotonic (\k -> k + dummyShift) afterPreds
      ]

    incomingSuccs' =
      M.foldWithKey (\d ve succs -> case ve of
        Dummy pred -> M.adjust (\_ -> Dummy (d + dummyShift)) pred succs
        _          -> succs)
        (incomingSuccs ng)
        afterPreds

    -- TODO: This and g' should sort of be done in one pass.
    incomingSuccs'' =
      foldl (\m (i, (v, _)) -> case v of
        Dummy dum -> M.adjust (\_ -> Dummy i) dum m
        _         -> m)
      incomingSuccs'
      (zip [d0..] (incoming vGoodData))

{-
    g' =
      M.mapWithKey (\r vd -> vd { incoming = map (first (rename r)) (incoming vd) }) (M.delete vGood g)
      where
      rename rCurr ve = case ve of
        Real r ->
          if r == vGood
          then Dummy (d0 + fromJust (findIndex (== Real rCurr) (map fst . outgoing $ vGoodData)))
          else ve
        Dummy d ->
          if d >= d0 + dummiesRemoved then Dummy (d + dummyShift) else ve -}

{-
    g' =
      M.foldWithKey (\d ve digY'all -> case ve of
        Real r -> M.adjust (updateOutgoingAtAll (Dummy d) (Dummy (d + dummyShift))) r digY'all
        _      -> digY'all)
        (M.delete vGood g) afterPreds
-}
    g' =
      foldl (\digY'all r ->
        M.adjust (\vd -> vd { outgoing = map (first shift) (outgoing vd) }) r digY'all)
        g
        (List.nub . mapMaybe (\case {Real r -> Just r; _ -> Nothing}) $ M.elems afterPreds)
      where
      shift ve = case ve of
        Dummy d -> if d >= d0 + dummiesRemoved then Dummy (d + dummyShift) else ve
        _       -> ve

    g'' =
      foldl (\digY'all (i, (v, _)) -> case v of
        Real r -> M.adjust (updateOutgoingAtFirst (Real vGood) (Dummy i)) r digY'all
        _      -> digY'all)
        g'
        (zip [d0..] (incoming vGoodData))

    goodProgram = makeBottomGoodProgram vGoodData
  where
  -- TODO: This algorithm is a bit complicated. We could actually just use
  -- the rightmost good vertex rule and that would simplify this a bit.
  -- It's essentially an optimization to start by examining the successors
  -- of the incoming ports.

  (k, ng) = countAndDropFMapStraights $ dropComponentStraights ng0
  g       = digraph ng
  inSuccs = incomingSuccs ng

  -- If there are no vertices emanating from the incoming ports, then
  -- the graph is a natural transformation from the identity, but there
  -- are of course non-trivial such things. So, we must just pick a vertex
  -- in the graph which has no incoming vertices. It is best to pick the
  -- rightmost such vertex to prevent unnecessary fmapping.

  -- A vertex is top-good if all of its predecessors are dummys or orphans
  -- and its dummy predecessors form a contiguous block.
  -- A vertex is bottom-good if all of its all of its successors are dummys or childless.
  -- If a graph is non-trival (i.e., not a bunch of straights) then either there is
  -- a top-good vertex which is a successor of an incoming dummy, or
  -- a bottom-good vertex which is a predecessor of an outgoing dummy.
  -- More specifically, after stripping straights, the situation breaks up into the following cases.
  -- 1. There are incoming dummys.
  --    In this case, there must be a topgood vertex and it will be
  --    a successor of an incoming dummy. findGoodVertexFromTop will find it
  --    and we can pull it up "offscreen"
  -- 2. There are no incoming dummys.
  --    In this case, there must be a bottomgood vertex. Furthermore, it
  --    will be the predecessor of an outgoing dummy.
  --    findGoodVertexFromBottom will find it and we can pull it down
  --    "offscreen"

  findGoodVertex ng =
    traceShowId $ case findGoodVertexFrom Top ng of
      Just x  -> Just (Top, x)
      Nothing -> fmap (Bottom,) (findGoodVertexFrom Bottom ng)

  findGoodVertexFrom dir ng = go 0 (M.toList verts) where
    go !n [] = Nothing
    go !n ((d, Real r) : vs) =
      let vd = lookupExn r g in
      if isGood vd
      then Just (n, d, r, vd)
      else go (n + 1) vs
    go _ ((_, Dummy _):_) = error ("findGoodVertexFrom " ++ show dir ++ ": Impossible case")

    isGood = case dir of { Top -> isTopGood; Bottom -> isBottomGood }
    verts  = case dir of { Top -> incomingSuccs ng; Bottom -> outgoingPreds ng }

    isBottomGood vd =
      all (\(v, _) -> isChildlessOrDummy v) (outgoing vd)
      && contiguous (mapMaybe (\case {(Dummy d,_) -> Just d; _ -> Nothing}) (outgoing vd))
    isChildlessOrDummy (Dummy _) = True
    isChildlessOrDummy (Real r)  = null . outgoing $ lookupExn r g

    isTopGood vd              =
      all (\(v, _) -> isOrphanOrDummy v) (incoming vd)
      && contiguous (mapMaybe (\case {(Dummy d,_) -> Just d; _ -> Nothing}) (incoming vd))
    isOrphanOrDummy (Dummy _) = True
    isOrphanOrDummy (Real r)  = null . incoming $ lookupExn r g

  makeTopGoodProgram vd = label vd <> loop (map fst (incoming vd))
    where
    loop = \case
      []             -> Id
      (Dummy d : vs) -> case loop vs of
        Id         -> Id
        Simple s   -> Compound ("fmap (" ++ s ++ ")")
        Compound s -> Compound ("fmap (" ++ s ++ ")")

      (Real r : vs)  -> label (lookupExn r g) <> loop vs

  -- All children of the given vertex are dummys or childless
  makeBottomGoodProgram vd = loop (map fst (outgoing vd)) <> label vd where
    loop = \case
      []             -> Id
      (Dummy d : vs) -> case loop vs of
        Id         -> Id
        Simple s   -> Compound ("fmap (" ++ s ++ ")")
        Compound s -> Compound ("fmap (" ++ s ++ ")")
      (Real r : vs) -> loop vs <> label (lookupExn r g)

  fmapped n f = case n of
    0 -> f
    1 -> Compound ("fmap " ++ wrapped)
    _ -> Compound (parens (intercalate " . " $ replicate n "fmap") ++ wrapped)
    where wrapped = case f of { Simple x -> x; Compound x -> parens x }

  parens x = "(" ++ x ++ ")"

-- renameIncomingAt r g f = M.adjust (\vd -> vd { incoming = map (first f) (incoming vd) }) r g
renameIncoming g f = M.map

dropComponentStraights ng =
  let numComponentStraights =
        length $ takeWhile (\((dumIn,inSucc), (dumOut, outPred)) -> case (inSucc, outPred) of
          (Dummy dumOut', Dummy dumIn') -> dumOut' == dumOut
          _ -> False)
          (zip (M.toDescList (incomingSuccs ng)) (M.toDescList (outgoingPreds ng)))

      incoming' = M.fromList . drop numComponentStraights $ M.toDescList (incomingSuccs ng)
      outgoing' = M.fromList . drop numComponentStraights $ M.toDescList (outgoingPreds ng)
  in
  ng { incomingSuccs = incoming', outgoingPreds = outgoing' }

countAndDropFMapStraights :: NaturalGraph f -> (Int, NaturalGraph f)
countAndDropFMapStraights ng =
  let numFMapStraights =
        length $ takeWhile (\((dumIn,inSucc), (dumOut, outPred)) -> case (inSucc, outPred) of
          (Dummy dumOut', Dummy dumIn') -> dumOut' == dumOut
          _ -> False)
          (zip (M.toAscList (incomingSuccs ng)) (M.toAscList (outgoingPreds ng)))

      incoming' = M.fromList . drop numFMapStraights $ M.toAscList (incomingSuccs ng)
      outgoing' = M.fromList . drop numFMapStraights $ M.toAscList (outgoingPreds ng)
  in
  (numFMapStraights, ng { incomingSuccs = incoming', outgoingPreds = outgoing' })

{-
countAndDropFMapStraights ng =
  let inSuccs = incomingSuccs ng
      (length -> k, M.fromAscList -> incoming') = span (\(_,v) -> case v of { Dummy _ -> True; _ -> False }) $ M.toAscList inSuccs
      outgoing' = let o = outgoingPreds ng in
        if M.null o then M.empty else snd $ M.split (fst (M.findMin o) + k - 1) o
  in
  (k, ng { incomingSuccs = incoming' , outgoingPreds = outgoing'})
-}
-- TODO: This breaks the assumption that the vertices are labelled 1..n.
compressPaths :: NaturalGraph f -> NaturalGraph f
compressPaths ng = let g' = evalState (go $ digraph ng) (S.empty, []) in ng { digraph = g' }
  where
  outPreds = outgoingPreds ng
  go g = do
    (_, next) <- get
    case next of
      []       -> return g
      (Dummy d : vs) -> do
        let Just v = M.lookup d outPreds
        case v of
          Dummy _ -> return g
          Real r  -> slurpBackFrom r g

      (Real r : vs) -> slurpBackFrom r g

  slurpBackFrom = \v g -> do
    (seen, next) <- get
    let Just vd            = M.lookup v g
        (vdInit, labs, g') = slurp vd g
        vsNext             = filter (`S.member` seen) (map fst (incoming vdInit))
        lab'               = label vd <> mconcat labs
        g''                = M.insert v (vd { incoming = incoming vdInit, label = lab' }) g'

    put (foldl' (flip S.insert) seen vsNext, vsNext ++ next)
    go g''
    where
    slurp vd g =
      case incoming vd of
        [(Real v',_)] ->
          let (vd', g')              = lookupDelete v' g
              (vdInit, labs, gFinal) = slurp vd' g'
          in
          (vdInit, label vd' : labs, gFinal)
        _ -> (vd, [], g)

  lookupDelete k m =
    let (Just x, m') = M.updateLookupWithKey (\_ _ -> Nothing) k m in (x, m')

-- isomorphic graphs will hash to the same value
-- TODO: There's either a bug in this or in isomorphic. There are more
-- unique hashes then the length of the nub by isomorphic
hashWithSaltGraph :: Hashable f => Int -> NaturalGraph f -> Int
hashWithSaltGraph s ng =
  let vs         = M.elems $ incomingSuccs ng
      (s', _, _) = execState go (s, S.fromList vs, vs)
  in s'
  where
  g  = digraph ng
  go = do
    (s, pushed, next) <- get
    case next of
      []                -> return ()

      (Dummy d : next') ->
        put (s `hashWithSalt` d, pushed, next') >> go

      (Real v : next') -> do
        let Just vd    = M.lookup v g
            s'         = s `hashWithSalt` label vd
            (s'', new) = foldl f' (foldl f (s',[]) (incoming vd)) (outgoing vd)
            pushed'    = foldl (\s x -> S.insert x s) pushed new
        put (s'', pushed', new ++ next')
        go
        where
        f (!salt, !xs) (x,lab) =
          ( salt `hashWithSalt` lab
          , case x of { Dummy _ -> xs; _ -> if x `S.member` pushed then xs else (x:xs) })

        f' (!salt, !xs) (x,lab) =
          ( salt `hashWithSalt` lab
          , if x `S.member` pushed then xs else (x:xs) )

-- all we need to do is use something more canonical for Vertex IDs and
-- isomorphism becomes equality. perhaps some coordinates involving the
-- length of the shortest path to the vertex?
isomorphic :: NaturalGraph f -> NaturalGraph f -> Bool
isomorphic ng1 ng2
  | incomingCount ng1 /= incomingCount ng1 || outgoingCount ng1 /= outgoingCount ng2  = False
  | otherwise =
    isRight . runIdentity . runErrorT $
      let vs1 = M.elems (incomingSuccs ng1)
          vs2 = M.elems (incomingSuccs ng2)
      in
      evalStateT go
        ( S.fromList vs1
        , zip vs1 vs2
        )
  where
  g1 = digraph ng1
  g2 = digraph ng2
  -- Sometimes I am an imperative programmer
  go :: StateT (S.Set Vert, [(Vert,Vert)]) (ErrorT String Identity) ()
  go = do
    (inQueue, next) <- get
    case next of
      [] -> return ()

      -- Have to make sure never to put an incoming dummy in the queue
      -- since there's no way to distinguish it from an outgoing dummy.
      -- Come to think of it, is there ever any need to actually do
      -- anything with outgoing Dummys? I don't think so. Just need to
      -- check that real vertices have Dummys in the right places.
      ((Dummy v1, Dummy v2) : next') -> do
        case (M.lookup v1 (outgoingPreds ng1), M.lookup v2 (outgoingPreds ng2)) of
          (Just (Dummy _), Just (Dummy _)) -> put (inQueue, next') >> go
          -- This seems wrong. I think it should never push anything.
          (Just v1', Just v2')             -> put (S.insert v1' inQueue, (v1', v2') : next') >> go
          _                                -> throwError "Something fishy"

      ((Real v1,Real v2) : next') -> do
        let Just vd1 = M.lookup v1 g1
            Just vd2 = M.lookup v2 g2
        when (label vd1 /= label vd2) $ throwError "Different transes"
        ins  <- zipErr (map fst $ incoming vd1) (map fst $ incoming vd2)
        outs <- zipErr (map fst $ outgoing vd1) (map fst $ outgoing vd2)
        let new =
              filter (\(x, _) -> case x of {Dummy _ -> False; _ -> not (x `S.member` inQueue)}) ins
              ++ filter (\(x, _) -> not (x `S.member` inQueue)) outs
            inQueue' = foldl (\s (x,_) -> S.insert x s) inQueue new
        put (inQueue', new ++ next')
        go

      _ -> throwError "Expected both real or both dummy"
    where
    zipErr xs ys =
      if length xs == length ys then return (zip xs ys) else throwError "zipErr"

-- Es importante que no cambia (incomingDummys ng1) o
-- (outgoingDummys ng2)

shiftBy n g =
  M.map (\vd -> vd { incoming = shiftEs (incoming vd), outgoing = shiftEs (outgoing vd) })
  $ M.mapKeysMonotonic (+ n) g
  where
  shiftEs = map (\(v,f) -> (case v of {Real r -> Real (r + n); _ -> v}, f))

idName i = "net" ++ show i

graphToJSON :: NaturalGraph String -> Value
graphToJSON (NaturalGraph {..}) = 
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
    ++ map (\(i, vd) -> nodeObj ("real" ++ show i) (label vd) "gray") (M.toList digraph)

  edges =
    concatMap (\(v, vd) -> map (\(u,f) ->
      edgeObj ("real" ++ show v)
        (case u of { Real r -> "real" ++ show r; Dummy d -> "out" ++ show d })
        f) (outgoing vd))
      (M.toList digraph)
    ++ map (\(lab, (i, vert)) -> 
        let v = case vert of {Dummy d -> "out" ++ show d; Real r -> "real" ++ show r} in
        edgeObj ("in" ++ show i) v lab)
        (zip incomingLabels $ M.toList incomingSuccs)

graphToJS id ng = mconcat
  [ "network = new vis.Network("
  , "document.getElementById(" ,  show id , "),"
  , map (toEnum . fromEnum) . BL.unpack $ encode (graphToJSON ng)
  , ",{});"
  ]

graphsToHTML ngs =
  let js = unlines $ zipWith graphToJS (map idName [0..]) ngs
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
  ,   unlines $ zipWith (\i ng ->
        "<div>"
        ++ "<div class='network' id=" ++ show (idName i) ++ "></div>" 
        ++ "<div>" ++ renderTerm (toTerm ng) ++ "</div>"
        ++ "</div>"
        ) [0..] ngs
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

  (replacements, outgoingPreds', incomingSuccs') =
    foldl upd
      ( M.empty
      , M.map (\case {Real v -> Real (n1+v); x -> x}) (outgoingPreds ng2)
      , incomingSuccs ng1)
      [0..(M.size outPreds1)]

  digraph' =
    M.foldWithKey (\r (io, rep) g ->
      let replace = first $ \x -> case M.lookup x rep of
            Nothing -> x
            Just x' -> x'
      in
      case io of
        In  -> M.adjust (\vd -> vd { incoming = map replace (incoming vd) }) r g
        Out -> M.adjust (\vd -> vd { outgoing = map replace (outgoing vd) }) r g)
      (M.union g1 g2')
      replacements 

  -- There should really be a few pictures describing what this code does.

--  replacements :: Map RealVertex (InOrOut, Map Vert Vert)
  upd (replacements, outPreds, inSuccs) i =
    case (M.lookup i outPreds1, M.lookup i inSuccs2) of
      (Just x, Just y) -> case (x, y) of
        (Real u, Real v)    ->
          let v' = v + n1 in
          ( M.insertWith merge u (Out, M.singleton (Dummy i) (Real v'))
            $ M.insertWith merge v' (In, M.singleton (Dummy i) (Real u))
            $ replacements
          , outPreds
          , inSuccs
          )

        (Real u, Dummy d)   ->
          ( M.insertWith merge u (Out, M.singleton (Dummy i) (Dummy d)) replacements
          , M.insert d (Real u) outPreds
          , inSuccs
          )

        (Dummy d, Real v)   ->
          let v' = v + n1 in
          ( M.insertWith merge v' (In, M.singleton (Dummy i) (Dummy d)) replacements
          , outPreds
          , M.insert d (Real v') inSuccs
          )

        (Dummy d, Dummy d') ->
          ( replacements
          , M.insert d' (Dummy d) outPreds
          , M.insert d (Dummy d') inSuccs
          )

      _ -> (replacements, outPreds, inSuccs) -- TODO: This should throw an error actually
      where
      merge (io, replacements) (io', replacements') = (io, M.union replacements replacements')

{-
  -- TODO: This is wrong. It toe-steps.
  upd (g, outPreds, inSuccs) (i, func) =
    case (M.lookup i outPreds1, M.lookup i inSuccs2) of
      (Just x, Just y) -> case (x, y) of
        (Real u, Real v)    ->
          let v' = v + n1 in
          ( M.adjust (updateOutgoingAt (Dummy i) (Real v')) u 
            $ M.adjust (updateIncomingAt (Dummy i) (Real u)) v' g
          , outPreds
          , inSuccs
          )

        (Real u, Dummy d)   ->
          ( M.adjust (updateOutgoingAt (Dummy i) (Dummy d)) u g
          , M.insert d (Real u) outPreds
          , inSuccs
          )

        (Dummy d, Real v)   ->
          let v' = v + n1 in
          ( M.adjust (updateIncomingAt (Dummy i) (Dummy d)) v' g
          , outPreds
          , M.insert d (Real v') inSuccs
          )

        (Dummy d, Dummy d') ->
          ( g
          , M.insert d' (Dummy d) outPreds
          , M.insert d (Dummy d') inSuccs
          )

      _ -> (g, outPreds, inSuccs)
-}
-- TODO: Does this handle parallel edges properly? No. No it does not.
updateNeighborListAtAll x v es = map (\e@(y,f) -> if x == y then (v, f) else e) es

updateIncomingAtAll i v vd = vd { incoming = updateNeighborListAtAll i v (incoming vd) }
updateOutgoingAtAll i v vd = vd { outgoing = updateNeighborListAtAll i v (outgoing vd) }

updateNeighborListAtFirst x v = \case
  []          -> []
  e@(y, f):es -> if y == x then (v, f) : es else e : updateNeighborListAtFirst x v es

updateIncomingAtFirst x v vd = vd { incoming = updateNeighborListAtFirst x v (incoming vd) }
updateOutgoingAtFirst x v vd = vd { outgoing = updateNeighborListAtFirst x v (outgoing vd) }

contiguous (x:xs@(y:_)) = y == x + 1 && contiguous xs
contiguous _            = True

leftFromRight :: Eq a => [a] -> [a] -> Maybe [a]
leftFromRight (x : xs) [] = Nothing
leftFromRight (x : xs) (y : ys)
  | x == y    = leftFromRight xs ys
  | otherwise = Nothing
leftFromRight [] ys = Just ys

-- UTIL
-- lookupExn :: Ord k => k -> M.Map k v -> v
lookupExn k = fromMaybe (error ("M.lookup failed for key: " ++ show k)) . M.lookup (traceShowId k)
