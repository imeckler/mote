{-# LANGUAGE RecordWildCards, NamedFieldPuns, LambdaCase,
             ScopedTypeVariables, BangPatterns, ViewPatterns,
             TupleSections, DeriveFunctor, RankNTypes #-}
module Search.Graph where

import Prelude hiding (sequence)
import Data.Maybe
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Map (Map)
import Data.List
import Control.Applicative
import Control.Monad.State hiding (sequence)
import Control.Monad.Error hiding (sequence)
import Control.Monad.Identity hiding (sequence)
import Data.Array.MArray
import Data.Array.ST (STArray)
import Control.Monad.ST (ST, runST)
import qualified Data.List as List
import Data.Bifunctor
import Data.Either (isRight)

import Data.Monoid

import Data.Hashable
import qualified Data.HashSet as HashSet
import qualified Data.HashMap.Strict as HashMap

import Search.Util
import Search.Types
import Search.Graph.Types
import qualified Search.Word as Word
import Search.Word (Word(Word), InContext(..), View(..))

-- TODO: Perhaps add the ability to filter the results by those which
-- satisfy some test cases.


-- Vert is left ungeneralized for clarity
-- mapWordVertices :: (forall l. (Vert, l) -> x) -> Word (Vert, f) (Vert, o) -> Word x x

connectedComponents :: NaturalGraph f o -> [[UnambiguousVert]]
connectedComponents ng = go [] vs
  where
  go acc remaining = case S.maxView remaining of
    Nothing              -> acc
    Just (v, remaining') ->
      let comp = componentOf v ng in
      go (S.toList comp : acc) (S.difference remaining' comp)

  inSuccs  = incomingSuccs ng
  outPreds = outgoingPreds ng
  g        = digraph ng

  vs = S.fromList $ map UReal (M.keys g)
    ++ map (UDummy In) [0..(M.size inSuccs - 1)]
    ++ map (UDummy Out) [0..(M.size outPreds - 1)]

moveToGraph :: Move f o -> NaturalGraph f o
moveToGraph move = case move of
  Middle pre t post ->
    let (postSucc, trailingOuts) =
          case Word.end (to t) of
            Nothing ->
              (\i -> Clear (Dummy (nl + nt_o + i)), nr)
            Just _  ->
              (\_ -> CoveredInFog, 0)
    in
    NaturalGraph
    { incomingLabels = Word pre Nothing <> from t <> post
    , incomingSuccs = M.fromList $
        map (\i -> (i, Clear $ Dummy i)) [0..(nl - 1)]
        ++ map (\i -> (i, Clear $ Real 0)) [nl..(nl + nt_i - 1)]
        ++ map (\i -> (nl + nt_i + i, postSucc i))  [0..(nr - 1)]

    , outgoingPreds = M.fromList $
        map (\i -> (i, Clear $ Dummy i)) [0..(nl - 1)]
        ++ map (\i -> (i, Clear $ Real 0)) [nl..(nl + nt_o - 1)]
        ++ map (\i -> (nl + nt_o + i, Clear $ Dummy (nl + nt_i + i))) [0..(trailingOuts - 1)]

    , digraph = M.fromList
      [ ( 0
        , VertexData 
          { label    = name t
          , incoming =
              let Word fs mo = from t in
              Word (zipWith label [0..] fs) (fmap (label (nt_i - 1)) mo)
          , outgoing =
              let Word fs mo = to t in
              Word (zipWith label [0..] fs) (fmap (label (nt_o - 1)) mo)
          }
        )
      ]
    }
    where
    nl   = length pre
    nr   = Word.length post
    nt_i = Word.length (from t)
    nt_o = Word.length (to t)

    label i x = (Dummy (i + nl), x)


  End pre t ->
    NaturalGraph
    { incomingLabels = Word pre Nothing <> from t

    , incomingSuccs = M.fromList $
        map (\i -> (i, Clear $ Dummy i)) [0..(nl - 1)]
        ++ map (\i -> (i, Clear $ Real 0)) [nl..(nl + nt_i - 1)]

    , outgoingPreds = M.fromList $
        map (\i -> (i, Clear $ Dummy i)) [0..(nl - 1)]
        ++ map (\i -> (i, Clear $ Real 0)) [nl..(nl + nt_o - 1)]

    , digraph = M.fromList
        [ ( 0
          , VertexData
            { label = name t 
            , incoming =
                let Word fs mo = from t in
                Word (zipWith label [0..] fs) (fmap (label (nt_i - 1)) mo)

            , outgoing =
                let Word fs mo = from t in
                Word (zipWith label [0..] fs) (fmap (label (nt_o - 1)) mo)
            }
          )
        ]
    }
    where
    nl = length pre
    nt_i = Word.length (from t)
    nt_o = Word.length (to t)

    label i x = (Dummy (i + nl), x)

idGraph :: [f] -> NaturalGraph f o
idGraph fs =
  NaturalGraph
  { incomingLabels = Word fs Nothing
  , incomingSuccs = M.fromList $ map (\i -> (i, Clear $ Dummy i)) [0..n]
  , outgoingPreds = M.fromList $ map (\i -> (i, Clear $ Dummy i)) [0..n]
  , digraph = M.empty
  }
  where
  n = length fs - 1

branchOut
  :: (Eq f, Hashable f, Eq o, Hashable o)
  => HashMap.HashMap (Word f o) [Trans f o]
  -> Word f o
  -> [(Word f o, Move f o)]
branchOut ts = concatMap possibilities . Word.views
  where
  -- possibilities :: Word.View f o -> [(Word f o, Move f o)]
  possibilities wv = map newWordAndMove matches
    where
    matches = fromMaybe [] (HashMap.lookup focus ts)

    -- TODO: Can reduce branching by computing pre <> focus <> post inside
    -- the case

    -- TODO: Types not as tight as they could be. These cases really belong
    -- in separate functions

    -- Invariant : focus == from t
    (focus, newWordAndMove) = case wv of
      NoO pre foc post ->
        ( Word foc Nothing
        , \t ->
          (Word pre Nothing <> to t <> Word post Nothing, Middle pre t (Word post Nothing))
        )

      -- YesOMid and NoO can be unified with Middle, but it is a bit confusing.
      YesOMid pre foc post o ->
        ( Word foc Nothing
        , \t ->
          (Word pre Nothing <> to t <> Word post (Just o), Middle pre t (Word post (Just o)))
        )

      YesOEnd pre (foc, o) ->
        ( Word foc (Just o)
        , \t ->
          (Word pre Nothing <> to t, End pre t)
        )

-- Es importante que no cambia (incomingDummys ng1) o
-- (outgoingDummys ng2)

shiftBy n g =
  M.map (\vd -> vd { incoming = shiftEs (incoming vd), outgoing = shiftEs (outgoing vd) })
  $ M.mapKeysMonotonic (+ n) g
  where
  shift   = first $ \v -> case v of {Real r -> Real (r + n); _ -> v}
  shiftEs = bimap shift shift

spreadFog :: NaturalGraph f o -> NaturalGraph f o
spreadFog ng =
  _
  where
  ((dummyMay,hitConst), (toDelete,_)) =
    runState (travelUpTheRightCoast _) (S.empty, S.empty)

  (outPreds0, g0) =
    -- TODO: Possibly ineffecient. Use Map x () instead of Set so we can do
    -- Map.difference
    S.fold (\ve (outPreds', g') ->
      case ve of
        Dummy d ->
          (M.insert d CoveredInFog outPreds', g')
        Real r ->
          (outPreds', M.delete r g')
        )
        (outgoingPreds ng, g)
        toDelete

  (outPred1, g1) = 
    ( outPreds0 -- I think this is right...If the outpred of d was added to toDelete, then d was too
    , M.map (\vd ->
        _
        )
        g0 
    )

  -- State is things to speculatively delete on the right and things which
  -- we know we should delete on the left.
  -- The Bool is whether or not we actually traversed a constant functor edge 
  -- in our journey to the top right. If we did, we should delete
  -- everything to the right of the dummy.
  travelUpTheRightCoast :: Vert -> State (S.Set Vert, S.Set Vert) (Maybe DummyVertex, Bool)
  travelUpTheRightCoast ve = case ve of
    Dummy d ->
      return (Just d)

    Real r -> do
      result@(dummyMay,_) <-
        case mConst of
          Nothing ->
            loop vs

          Just (v,_) -> do
            (safe, speculative) <- get
            put (S.union safe speculative, S.empty)
            (md, _) <- travelUpTheRightCoast v
            return (md, True)

      case dummyMay of
        -- If all children fail, we should speculatively delete the current
        -- vertex.
        Nothing -> do
          (safe, speculative) <- get
          put (safe, S.insert ve speculative)

        Just _ ->
          return ()

      return result
      where
      Word vs mConst = incoming (lookupExn r g)

    where
    loop = \case
      [] -> do
        (safe, speculative) <- get
--        put (safe, S.insert ve speculative)
        return Nothing

      (v, _) : vs ->
        travelUpTheRightCoast v >>= \res@(md,_) -> case md of
          Just _ -> return res
          Nothing -> loop vs

  g = digraph ng

data FunctorType = Constant | NonConstant

{- begin debug
-- ng1 -> ng2
sequence :: NaturalGraph f o -> NaturalGraph f o -> NaturalGraph f o
sequence ng1 ng2 =
  NaturalGraph
  { incomingLabels = incomingLabels ng1
  , incomingSuccs  = incomingSuccs'

  , outgoingPreds  = outgoingPreds'

  , digraph        = digraph'
  }
  where
  g1  = digraph ng1
  g2  = digraph ng2
  g2' = shiftBy n1 g2
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
    
  upd (replacements, 

  -- TODO: Basically do the smae thing as before, then go "up and to the
  -- right from the rightmost outgoing dummy of the bottom graph and then
  -- mist out everything to the right
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
      merge (io, replacements) (_io', replacements') = (io, M.union replacements replacements')

-- TODO: Convert real Haskell programs into lists of moves
-- TODO: Analyze program graphs

graphsOfSizeAtMost
  :: (Hashable f, Ord f, Hashable o, Ord o)
  => [Trans f o]
  -> Int
  -> Word f o
  -> Word f o
  -> [NaturalGraph f o]
graphsOfSizeAtMost tsList n start end = map deleteStrayVertices . HashSet.toList $ runST $ do
  arr <- newSTArray (0, n) M.empty
  go arr n start
  where 
  newSTArray :: (Int, Int) -> Map k v -> ST s (STArray s Int (Map k v))
  newSTArray = newArray

  ts = HashMap.fromListWith (++) (map (\t -> (from t, [t])) tsList)

  -- TODO: This is wrong, should allow shit to happen after reaching the
  -- end.
  go arr n b
    | b == end  = return (HashSet.singleton (idGraph end))
    | n == 0    = return HashSet.empty
    | otherwise = do
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
graphsOfSizeAtMostH
  :: (Hashable f, Ord f, Hashable o, Ord o)
  => [Trans f o] -> Int -> Word f o -> Word f o
  -> [NaturalGraph f o]
graphsOfSizeAtMostH tsList n start end = map deleteStrayVertices . HashSet.toList $ runST $ do
  arr <- newSTArray (0, n) M.empty
  fmap HashSet.unions . forM (branchOut ts start) $ \(b', move@(_, t,_)) ->
    let g = moveToGraph move in
    fmap (HashSet.map (sequence g)) (go arr (n - 1) b' t)
  where 
  newSTArray :: (Int, Int) -> Map k v -> ST s (STArray s Int (Map k v))
  newSTArray = newArray

  ts = HashMap.fromListWith (++) (map (\t -> (from t, [t])) tsList)

  -- TODO: Some work is definitely duplicated.
  -- E.g., I start with AB, which gets rewritten to CB, to BC, to ABC, to
  -- AB, I shouldn't keep going since happens next should have been done up
  -- the call stack (or is about to be done).
  -- For each S, n store programs of length n which map out of S (to T), keyed by T
  go _   0 b _              = return $ if b == end then HashSet.singleton (idGraph end) else HashSet.empty
  go arr n b t = do
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
              fmap (HashSet.map (sequence g)) (go arr (n - 1) b' t')

          let progs' = if b == end then HashSet.insert (idGraph end) progs else progs
          writeArray arr n (M.insert b progs' memo)
          return progs'

      Just ps -> return ps

{-
TODO: Rewrite this function to work with the new changes
juxtapose :: NaturalGraph f o -> NaturalGraph f o -> NaturalGraph f o
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
-}

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

renderAnnotatedTerm = renderTerm . unannotatedTerm

toTerm :: NaturalGraph f o -> AnnotatedTerm
toTerm = toTerm' . compressPaths

-- Three cases:
-- There are incoming vertices
-- There are no incoming vertices but there are outgoing vertices
-- There are no 
-- there are no incoming vertices or outgoing vertices.
data TopOrBottom = Top | Bottom deriving (Eq, Show)

data GoodVertexType = FloatingRightOf Int | AttachedTo DummyVertex
toTerm' :: NaturalGraph f o -> AnnotatedTerm
toTerm' ng0 = case findGoodVertex ng of
  Nothing -> AnnotatedTerm Id 0
  Just (Top, (leftStrands, vGood, vGoodData)) ->
    case toTerm' ng' of
      (unannotatedTerm -> Id) -> fmapped (k + leftStrands) goodProgram
      p                       -> fmapped k (p <> fmapped leftStrands goodProgram)
    where
    dummiesRemoved = length . filter (\case {(Dummy _,_) -> True; _ -> False}) $ incoming vGoodData
    dummiesCreated = length $ outgoing vGoodData
    dummyShift     = dummiesCreated - dummiesRemoved

    -- leftStrands is the number of strands strictly to the left of the
    -- good vertex.
    -- I thought this was wrong and we have to case on whether its a free or
    -- attached vertex since in the attched case we delete a dummy strand
    -- and in the free case we don't. BUT, the fact that dummiesRemoved is
    -- 0 in the free case actually takes care of that
    (beforeSuccs, afterSuccs) =
      let (before, _) = M.split leftStrands (incomingSuccs ng)
          (_, after)  = M.split (leftStrands + dummiesRemoved - 1) (incomingSuccs ng)
      in
      (before, after)

    incomingSuccs' =
      M.unions
      [ beforeSuccs
      , M.fromList $ zipWith (\i (v,_) -> (i, v)) [leftStrands..] (outgoing vGoodData)
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
        (zip [leftStrands..] (outgoing vGoodData))

    g' =
      foldl (\digY'all r ->
        M.adjust (\vd -> vd { incoming = map (first shift) (incoming vd) }) r digY'all)
        (M.delete vGood g)
        (List.nub . mapMaybe (\case {Real r -> Just r; _ -> Nothing}) $ M.elems afterSuccs)
      where
      shift ve = case ve of
        Dummy d -> if d >= leftStrands + dummiesRemoved then Dummy (d + dummyShift) else ve
        _       -> ve

    g'' =
      foldl (\digY'all (i, (v,_)) -> case v of
        Real r -> M.adjust (updateIncomingAtFirst (Real vGood) (Dummy i)) r digY'all 
        _      -> digY'all)
        g'
        (zip [leftStrands..] (outgoing vGoodData))

    ng' = ng { incomingSuccs = incomingSuccs', digraph = g'', outgoingPreds = outgoingPreds'' }

    goodProgram = makeTopGoodProgram vGoodData

  Just (Bottom, (leftStrands, vGood, vGoodData)) ->
    case toTerm ng' of
      (unannotatedTerm -> Id) -> fmapped (k + leftStrands) goodProgram -- I think n will always be 0 in this case
      p  -> fmapped k (fmapped leftStrands goodProgram <> p)
    where
    dummiesCreated = length $ incoming vGoodData
    dummiesRemoved = length . filter (\case {(Dummy _,_) -> True; _ -> False}) $ outgoing vGoodData
    dummyShift     = dummiesCreated - dummiesRemoved

    (beforePreds, afterPreds) =
      let (before, _) = M.split leftStrands (outgoingPreds ng)
          (_, after)  = M.split (leftStrands + dummiesRemoved - 1) (outgoingPreds ng)
      in
      (before, after)

    outgoingPreds' =
      M.unions
      [ beforePreds
      , M.fromList $ zipWith (\i (v,_) -> (i, v)) [leftStrands..] (incoming vGoodData)
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
      (zip [leftStrands..] (incoming vGoodData))

    g' =
      foldl (\digY'all r ->
        M.adjust (\vd -> vd { outgoing = map (first shift) (outgoing vd) }) r digY'all)
        (M.delete vGood g)
        (List.nub . mapMaybe (\case {Real r -> Just r; _ -> Nothing}) $ M.elems afterPreds)
      where
      shift ve = case ve of
        Dummy d -> if d >= leftStrands + dummiesRemoved then Dummy (d + dummyShift) else ve
        _       -> ve

    g'' =
      foldl (\digY'all (i, (v, _)) -> case v of
        Real r -> M.adjust (updateOutgoingAtFirst (Real vGood) (Dummy i)) r digY'all
        _      -> digY'all)
        g'
        (zip [leftStrands..] (incoming vGoodData))

    ng' = ng { incomingSuccs = incomingSuccs'', digraph = g'', outgoingPreds = outgoingPreds' }

    -- TODO: This should be eliminated since now good vertices have no
    -- orphan parents
    goodProgram = makeBottomGoodProgram vGoodData
  where
  -- TODO: This algorithm is a bit complicated. We could actually just use
  -- the rightmost good vertex rule and that would simplify this a bit.
  -- It's essentially an optimization to start by examining the successors
  -- of the incoming ports.

  (k, ng) = countAndDropFMapStraights $ dropComponentStraights ng0
  g       = digraph ng

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
    case findGoodVertexFrom Top ng of
      Just x  -> Just (Top, x)
      Nothing -> fmap (Bottom,) (findGoodVertexFrom Bottom ng)

  -- TODO: When I have the chance, it should preferentially pull a good vertex up if it
  -- reduces the number of incoming ports

  -- this scans from left to right. 
  -- should keep track of the rightmost dummy thread which we are at least
  -- as far right as.

  -- d here is the index of the rightmost dummy we've seen.
  findGoodVertexFrom dir ng =
    if M.size start == 0
    then Nothing
    else foldr (\(d, ve) keepGoing -> case ve of
      Real r -> go d r <|> keepGoing
      Dummy _ -> keepGoing)
      Nothing
      (M.toAscList start)
    where
    scanAcross _d []           = Nothing
    scanAcross d ((ve,_) : vs) = case ve of
      Real r   -> Just (d, r)
      Dummy d' -> scanAcross (max d d') vs -- I think d' always wins. I.e., d' == max d d'

    -- d is the number of strands strictly to the left of us
    go d r =
      let vd = lookupExn r g in
      case next vd of
        [] -> Just (d, r, vd) -- Just (d + 1, r, vd)
        xs -> case scanAcross d xs of
          Nothing       -> 
            if contiguous (map (\(Dummy d,_) -> d) xs)
            then let (Dummy dum, _) = head xs in Just (dum, r, vd)
            else Nothing
          Just (d', r') -> go d' r'

    start = case dir of { Top -> incomingSuccs ng; Bottom -> outgoingPreds ng }
    next  = case dir of { Top -> incoming; Bottom -> outgoing }

  makeTopGoodProgram vd = label vd <> loop (map fst (incoming vd))
    where
    loop = \case
      []             -> AnnotatedTerm Id 0
      (Dummy _ : vs) -> let AnnotatedTerm t x = loop vs in case t of
        Id         -> AnnotatedTerm Id x
        Simple s   -> AnnotatedTerm (Compound ("fmap (" ++ s ++ ")")) x
        Compound s -> AnnotatedTerm (Compound ("fmap (" ++ s ++ ")")) x

      (Real r : vs)  -> label (lookupExn r g) <> loop vs

  -- All children of the given vertex are dummys or childless
  makeBottomGoodProgram vd = loop (map fst (outgoing vd)) <> label vd where
    loop = \case
      []             -> AnnotatedTerm Id 0

      (Dummy _ : vs) -> let AnnotatedTerm t x = loop vs in case t of
        Id         -> AnnotatedTerm Id x
        Simple s   -> AnnotatedTerm (Compound ("fmap (" ++ s ++ ")")) x
        Compound s -> AnnotatedTerm (Compound ("fmap (" ++ s ++ ")")) x

      (Real r : vs) -> loop vs <> label (lookupExn r g)

  fmapped n (AnnotatedTerm f x) = case n of
    0 -> AnnotatedTerm f x
    1 -> AnnotatedTerm (Compound ("fmap " ++ wrapped)) x
    _ -> AnnotatedTerm (Compound (parens (intercalate " . " $ replicate n "fmap") ++ " " ++ wrapped)) x
    where wrapped = case f of { Simple x -> x; Compound x -> parens x; _ -> error "Search.Graph.fmapped: Impossible" }

  parens x = "(" ++ x ++ ")"

-- Maintaining the invariant that the dummys are labelled 0..n
dropComponentStraights ng =
  let numComponentStraights =
        length $ takeWhile (\((_dumIn, inSucc), (dumOut, outPred)) -> case (inSucc, outPred) of
          (Dummy dumOut', Dummy _dumIn') -> dumOut' == dumOut
          _ -> False)
          (zip (M.toDescList (incomingSuccs ng)) (M.toDescList (outgoingPreds ng)))

      incoming' = M.fromList . zip [0..] . map snd . reverse . drop numComponentStraights $ M.toDescList (incomingSuccs ng)
      outgoing' = M.fromList . zip [0..] . map snd . reverse . drop numComponentStraights $ M.toDescList (outgoingPreds ng)
  in
  ng { incomingSuccs = incoming', outgoingPreds = outgoing' }

countAndDropFMapStraights :: NaturalGraph f o -> (Int, NaturalGraph f o)
countAndDropFMapStraights ng =
  let numFMapStraights =
        length $ takeWhile (\((_dumIn, inSucc), (dumOut, outPred)) -> case (inSucc, outPred) of
          (Dummy dumOut', Dummy _dumIn') -> dumOut' == dumOut
          _ -> False)
          (zip (M.toAscList (incomingSuccs ng)) (M.toAscList (outgoingPreds ng)))

      incoming' = M.fromList . zip [0..] . map snd . drop numFMapStraights $ M.toAscList (incomingSuccs ng)
      outgoing' = M.fromList . zip [0..] . map snd . drop numFMapStraights $ M.toAscList (outgoingPreds ng)

      shift = first $ \ve -> case ve of
        Dummy d -> Dummy (d - numFMapStraights)
        _       -> ve

      g' = M.map (\vd -> vd { incoming = map shift (incoming vd), outgoing = map shift (outgoing vd) }) (digraph ng)
  in
  ( numFMapStraights
  , ng { incomingSuccs = incoming', outgoingPreds = outgoing', digraph = g' }
  )

-- TODO: This breaks the assumption that internal vertices are labelled 0..n, but I don't
-- think I ever use that assumption
compressPaths :: NaturalGraph f o -> NaturalGraph f o
compressPaths ng = let g' = evalState (go $ digraph ng) (S.empty, []) in ng { digraph = g' }
  where
  outPreds = outgoingPreds ng
  go g = do
    (_, next) <- get
    case next of
      []       -> return g
      (Dummy d : _) -> do
        let Just v = M.lookup d outPreds
        case v of
          Dummy _ -> return g
          Real r  -> slurpBackFrom r g

      (Real r : _) -> slurpBackFrom r g

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


-- all we need to do is use something more canonical for Vertex IDs and
-- isomorphism becomes equality. perhaps some coordinates involving the
-- length of the shortest path to the vertex?
isomorphic :: NaturalGraph f o -> NaturalGraph f o -> Bool
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


updateNeighborListAtAll x v es = map (\e@(y,f) -> if x == y then (v, f) else e) es

{-
updateIncomingAtAll i v vd = vd { incoming = updateNeighborListAtAll i v (incoming vd) }
updateOutgoingAtAll i v vd = vd { outgoing = updateNeighborListAtAll i v (outgoing vd) }
-}

updateNeighborListAtFirst x v = \case
  []          -> []
  e@(y, f):es -> if y == x then (v, f) : es else e : updateNeighborListAtFirst x v es

updateNeighborWordAtFirst x v (Word fs mo) =
  case mo of
    Nothing     -> Word (updateNeighborListAtFirst x v fs) Nothing
    Just (y, o) -> if y == x then Word fs (Just (v,o)) else Word (updateNeighborListAtFirst x v fs) mo

updateIncomingAtFirst x v vd = vd { incoming = updateNeighborWordAtFirst x v (incoming vd) }
updateOutgoingAtFirst x v vd = vd { outgoing = updateNeighborWordAtFirst x v (outgoing vd) }

contiguous (x:xs@(y:_)) = y == x + 1 && contiguous xs
contiguous _            = True

leftFromRight :: Eq a => [a] -> [a] -> Maybe [a]
leftFromRight (_ : _) [] = Nothing
leftFromRight (x : xs) (y : ys)
  | x == y    = leftFromRight xs ys
  | otherwise = Nothing
leftFromRight [] ys = Just ys
end debug -} 
{-
checkGraph :: (Show o, Show f) => NaturalGraph f o -> Either String ()
checkGraph ng = do
  throwIfNot "Incoming bad" $ all (uncurry (==)) $ zip [0..] (M.keys (incomingSuccs ng))
  throwIfNot "Outgoing bad" $ all (uncurry (==)) $ zip [0..] (M.keys (outgoingPreds ng))
  forM_ (M.toList (incomingSuccs ng)) $ \(dum, ve) ->
    case ve of
      Dummy d ->
        throwIfNot "Dummy out didn't agree with dummy in" $
          M.lookup d (outgoingPreds ng) == Just (Dummy dum)
      Real r -> do
        vd <- lookupThrow r g
        throwIfNot "Out suc didn't think it was coming in" $
          Dummy dum `elem` map fst (incoming vd)

  forM_ (M.toList (outgoingPreds ng)) $ \(dum, ve) ->
    case ve of
      Dummy d ->
        throwIfNot "Dummy out didn't agree with dummy in" $
          M.lookup d (incomingSuccs ng) == Just (Dummy dum)
      Real r -> do
        vd <- lookupThrow r g
        throwIfNot "Out suc didn't think it was coming in" $
          Dummy dum `elem` map fst (outgoing vd)

  forM_ (M.toList g) $ \(v, vd) -> do
    forM_ (incoming vd) $ \(ve, _) -> case ve of
      Dummy d ->
        throwIfNot ("Disagreement: " ++ show v ++ " has pred Dummy " ++ show d ++ " but Dummy does not have it as suc") $
          M.lookup d (incomingSuccs ng) == Just (Real v)

      Real r -> do
        vd' <- lookupThrow r g
        throwIfNot "Am I Not your neighbor" $
          Real v `elem` map fst (outgoing vd')

    forM_ (outgoing vd) $ \(ve, _) -> case ve of
      Dummy d ->
        throwIfNot ("Disagreement: " ++ show v ++ " has suc Dummy " ++ show d ++ " but Dummy does not have it as pred") $
          M.lookup d (outgoingPreds ng) == Just (Real v)

      Real r -> do
        vd' <- lookupThrow r g
        throwIfNot "Am I Not your neighbor" $
          Real v `elem` map fst (incoming vd')
  where
  lookupThrow r g = case M.lookup r g of
    Nothing -> Left ("I got nothing for: " ++ show r)
    Just x  -> Right x

  throwIf e x  = if x then Left e else Right ()
  throwIfNot e = throwIf e . not
  g = digraph ng
-}
-- UTIL
-- lookupExn :: Ord k => k -> M.Map k v -> v
