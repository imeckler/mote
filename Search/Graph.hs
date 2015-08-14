{-# LANGUAGE RecordWildCards, NamedFieldPuns, LambdaCase,
             ScopedTypeVariables, BangPatterns, ViewPatterns,
             TupleSections, DeriveFunctor, RankNTypes,
             NoMonomorphismRestriction, FlexibleContexts #-}
module Search.Graph where

import Prelude hiding (sequence, Word)
import Data.Maybe
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Map (Map)
import Control.Applicative
import Control.Monad (forM, mfilter)
import Data.Array.MArray
import Data.Array.ST (STArray)
import Control.Monad.ST (ST, runST)
import qualified Data.List as List
import Data.Bifunctor

import Data.Monoid

import Data.Hashable
import qualified Data.HashSet as HashSet
import qualified Data.HashMap.Strict as HashMap

import Search.Util
import Search.Types
import Search.Graph.Types
import qualified Search.Types.Word as Word
import Search.Types.Word (Word(Word), InContext(..), View(..))

import Search.Graph.Canonicalize
import Search.Graph.Types.NeighborList (NeighborList(..))
import qualified Search.Graph.Types.NeighborList as NeighborList

import Debug.Trace
import qualified Search.Graph.ToTerm as ToTerm

-- TODO: Biggest todo. Polymorphism and fanout. Should be able to use projections eg.
-- I will be happy when search can find a program of type
-- [(Int,a)] -> (Int,[a]). Hopefully the one \xs -> (sum xs, map snd xs)

-- TODO: Consider detecting when things are destructive (e.g., !! or head)
-- or trivial (e.g., maybeToList) to weight terms differently

-- TODO: Perhaps add the ability to filter the results by those which
-- satisfy some test cases.

toTerm :: NaturalGraph f o -> AnnotatedTerm
toTerm = ToTerm.toTerm . compressPaths


moveSequenceToAnnotatedTerm :: [Move f o] -> AnnotatedTerm
moveSequenceToAnnotatedTerm = foldMap moveToTerm . reverse
  where
  moveToTerm :: Move f o -> AnnotatedTerm
  moveToTerm mv =
    case mv of
      Word.Middle pre t post -> ToTerm.fmapped (length pre) (name t)
      Word.End pre t -> ToTerm.fmapped (length pre) (name t)

-- Vert is left ungeneralized for clarity
-- mapWordVertices :: (forall l. (Vert, l) -> x) -> Word (Vert, f) (Vert, o) -> Word x x

connectedComponents :: NaturalGraph f o -> [Set.Set UnambiguousVert]
connectedComponents ng = go [] vs
  where
  vs = 
    Set.fromList $
      mapMaybe (disambiguate In) (NeighborList.toList (top ng))
      ++ mapMaybe (disambiguate Out) (NeighborList.toList (bottom ng))

  go acc remaining =
    case Set.minView remaining of
      Just (uv, remaining') ->
        let comp = componentOf uv ng in
        go (comp : acc) (remaining' `Set.difference` comp) 

      Nothing -> acc


-- TODO: This should really just take the dummy edge as an arg.
componentOf :: UnambiguousVert -> NaturalGraph f o -> Set.Set UnambiguousVert
componentOf v ng = go Set.empty [v]
  where
  g = digraph ng

  edgeInfo = edges ng

  go :: Set.Set UnambiguousVert -> [UnambiguousVert] -> Set.Set UnambiguousVert
  go seen uvs =
    case uvs of
      [] -> seen
      uv : uvs' ->
        if uv `Set.member` seen
        then go seen uvs'
        else
          let
            next =
              case uv of
                UReal v ->
                  let VertexData {incoming, outgoing} = lookupExn' "Graph:93" v g
                  in
                  mapMaybe (disambiguate In) (NeighborList.toList incoming)
                  ++ mapMaybe (disambiguate Out) (NeighborList.toList outgoing)

                UDummy io e ->
                  let EdgeData {source,sink} = lookupExn' "Graph:99" e edgeInfo
                  in
                  case io of
                    In -> mapMaybe (disambiguate Out) [(sink, e)]
                    Out -> mapMaybe (disambiguate In) [(source, e)]
          in
          go (Set.insert uv seen) (next ++ uvs')

disambiguate :: InOrOut -> (Foggy (OrBoundary Vertex), EdgeID) -> Maybe UnambiguousVert
disambiguate io (fbv, e) =
  case fbv of
    Clear Boundary ->
      Just (UDummy io e)

    Clear (Inner v) ->
      Just (UReal v)

    CoveredInFog ->
      Nothing

-- TODO: Unify cases
moveToGraph :: Move f o -> NaturalGraph f o
moveToGraph move = case move of
  Middle pre t post ->
    NaturalGraph
    -- If we're in this case, end (from t) and end (to t) cannot be Just
    -- since post should then be empty (when it can't really)
    { top =
        NoFogged
          ( Word (zipWith (\f i -> (Boundary, (i, f))) pre [0..]) Nothing
            <> bimap (Inner 0,) (Inner 0,) edgedFrom
            <> bimap (Boundary,) (Boundary,) (enum_word (n_l + n_mid_in + n_mid_out) post))
            
    , bottom =
        NoFogged
          ( Word (zipWith (\f i -> (Boundary, (i, f))) pre [0..]) Nothing
          <> bimap (Inner 0,) (Inner 0,) edgedTo
          <> bimap (Boundary,) (Boundary,) (enum_word (n_l + n_mid_in + n_mid_out) post))
    
    , digraph =
      Map.singleton 0 $
        VertexData
        { label = name t
        , incoming = NoFogged (bimap (Boundary,) (Boundary,) edgedFrom)
        , outgoing = NoFogged (bimap (Boundary,) (Boundary,) edgedTo)
        }

    , edges =
        Map.fromAscList $
             map (\i -> (i, EdgeData {source=Clear Boundary,sink=Clear Boundary})) [0..(n_l - 1)]
          ++ map (\i -> (i, EdgeData {source=Clear Boundary,sink=Clear (Inner 0)})) [n_l..(n_l + n_mid_in - 1)]
          ++ map (\i -> (i, EdgeData {source=Clear (Inner 0),sink=Clear Boundary})) [(n_l + n_mid_in)..(n_l + n_mid_in + n_mid_out - 1)]
          ++ map (\i -> (i, EdgeData {source=Clear Boundary,sink=Clear Boundary})) [(n_l + n_mid_in + n_mid_out)..(n_l + n_mid_in + n_mid_out + n_r - 1)]
    
    , constantEdges =
        Set.fromList $
          catMaybes
          [ (n_l + n_mid_in - 1) <$ Word.end (from t)
          , (n_l + n_mid_in + n_mid_out - 1) <$ Word.end (to t)
          ]

    , freshVertex = 1

    , freshEdgeID = n_l + n_mid_in + n_mid_out + n_r
    }
    where
    n_l = length pre
    n_mid_in = Word.length (from t)
    n_mid_out = Word.length (to t)
    n_r = Word.length post

    edgedFrom = 
      let Word fs mo = from t in
      Word (zipWith (\f i -> (i, f)) fs [n_l..])
        (fmap (\o -> (n_l + n_mid_in - 1,o)) mo)

    edgedTo =
      let Word fs mo = to t in
      Word (zipWith (\f i -> (i, f)) fs [(n_l + n_mid_in)..])
        (fmap (\o -> (n_l + n_mid_in + n_mid_out - 1,o)) mo)

    enum_word :: Int -> Word f o -> Word (Int, f) (Int, o)
    enum_word !i (Word fs mo) =
      case fs of
        []      -> Word [] (fmap (i,) mo)
        f : fs' -> let Word ifs imo = enum_word (i + 1) (Word fs' mo) in Word ((i,f):ifs) imo

  End pre t ->
    NaturalGraph
    { top =
        NoFogged
          ( Word (zipWith (\f i -> (Boundary, (i, f))) pre [0..]) Nothing
          <> bimap (Inner 0,) (Inner 0,) edgedFrom)
    , bottom  =
        NoFogged
          ( Word (zipWith (\f i -> (Boundary, (i, f))) pre [0..]) Nothing
          <> bimap (Inner 0,) (Inner 0,) edgedTo)

    , digraph =
        Map.singleton 0 $
        VertexData
        { label    = name t
        , incoming = NoFogged (bimap (Boundary,) (Boundary,) edgedFrom)
        , outgoing = NoFogged (bimap (Boundary,) (Boundary,) edgedTo)
        }

    , edges =
        Map.fromAscList
        $  map (\i -> (i, EdgeData {source=Clear Boundary,sink=Clear Boundary})) [0..(n_l - 1)]
        ++ map (\i -> (i, EdgeData {source=Clear Boundary,sink=Clear (Inner 0)}))  [n_l..(n_l + n_mid_in - 1)]
        ++ map (\i -> (i, EdgeData {source=Clear (Inner 0),sink=Clear Boundary})) [(n_l + n_mid_in)..(n_l + n_mid_in + n_mid_out - 1)]

    , constantEdges =
        Set.fromList $
          catMaybes
          [ (n_l + n_mid_in - 1) <$ Word.end (from t)
          , (n_l + n_mid_in + n_mid_out - 1) <$ Word.end (to t)
          ]

    , freshEdgeID = n_l + n_mid_in + n_mid_out

    , freshVertex = 1
    }
    where
    edgedFrom = 
      let Word fs mo = from t in
      Word (zipWith (\f i -> (i, f)) fs [n_l..])
        (fmap (\o -> (n_l + n_mid_in - 1,o)) mo)

    edgedTo =
      let Word fs mo = to t in
      Word (zipWith (\f i -> (i, f)) fs [(n_l + n_mid_in)..])
        (fmap (\o -> (n_l + n_mid_in + n_mid_out - 1,o)) mo)

    n_l       = length pre
    n_mid_in  = Word.length (from t)
    n_mid_out = Word.length (to t)


idGraph :: Word f o -> NaturalGraph f o
idGraph w =
  NaturalGraph
  { top =
      NoFogged
        (Word (zipWith (\i f -> (Boundary, (i,f))) [0..] fs)
          (fmap (\o -> (Boundary, (k-1,o))) mo))

  , bottom =
      NoFogged
        (Word (zipWith (\i f -> (Boundary, (i,f))) [0..] fs)
          (fmap (\o -> (Boundary, (k-1,o))) mo))

  , digraph = Map.empty

  , edges = Map.fromList (map (\i -> (i,EdgeData (Clear Boundary) (Clear Boundary))) [0..(k-1)])

  , constantEdges =
      maybe Set.empty (\_ -> Set.singleton (k - 1)) mo
  
  , freshEdgeID = k

  , freshVertex = 0
  }
  where
  k = Word.length w
  Word fs mo = w

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

shiftBy :: NaturalGraph f o -> Int -> Int -> NaturalGraph f o
shiftBy ng s_v s_e =
  ng
  -- TODO: Optimize to do only one traversal of the NeighborLists. better
  -- to make the vertices part of the functory data
  { top = shiftNeighborList (top ng)
  , bottom = shiftNeighborList (bottom ng)
  , digraph =
      Map.mapKeysMonotonic (+ s_v) $
        Map.map (\vd ->
          vd { incoming = shiftNeighborList (incoming vd), outgoing = shiftNeighborList (outgoing vd) } 
          )
          -- (bimap (first (+ s_e)) (first (+ s_e)))
          (digraph ng)
  , edges =
      Map.mapKeysMonotonic (+ s_e) $
        Map.map (\(EdgeData {source, sink}) ->
          EdgeData {source=fmap (fmap (+ s_v)) source,sink=fmap (fmap (+ s_v)) sink})
          (edges ng)

  , constantEdges = Set.mapMonotonic (+ s_e) (constantEdges ng)
  }
  where
  shiftNeighborList = 
    NeighborList.mapVertex (fmap (+ s_v)) . bimap (first (+ s_e)) (first (+ s_e))

-- sequence :: NaturalGraph f o -> NaturalGraph f o -> NaturalGraph f o
sequence ng1 ng2_0 =
  NaturalGraph
  { top           = top'
  , bottom        = bottom'
  , digraph       = digraph'
  , edges         = edges'
  , constantEdges =
      -- TODO: Use difference function
      Set.filter (`Map.member` edges')
        (Set.union (constantEdges ng1) (constantEdges ng2))
  , freshVertex = freshVertex ng1 + freshVertex ng2
  , freshEdgeID = freshEdgeID ng1 + freshEdgeID ng2
  }
  where
  ng2 = shiftBy ng2_0 (freshVertex ng1) (freshEdgeID ng1)

  discardLabel (v,(e,_)) = (v,e)

  (top', bottom', digraph', edges') =
    -- Should change this into a few lemmas so there aren't so many cases
    List.foldl' (\(newTop,newBot,g,edgeInfo) ((botPred, e1), (topSucc,e2)) ->
      case (botPred, topSucc) of
        (CoveredInFog, CoveredInFog) ->
          (newTop, newBot, g, Map.delete e1 (Map.delete e2 edgeInfo))

        (_, Clear Boundary) ->
          ( newTop
          , setAt e2 e1 botPred newBot
          , g
          , Map.delete e2 edgeInfo
          )

        -- e2 already has the correct edge data: Clear Boundary -> topSucc
        (Clear Boundary, _) ->
          ( setAt e1 e2 topSucc newTop
          , newBot
          , g
          , Map.delete e1 edgeInfo
          )

        (CoveredInFog, Clear (Inner v)) ->
          ( newTop
          , newBot
          , Map.adjust (\vd -> vd { incoming = setAt e2 e1 CoveredInFog (incoming vd) }) v g
          , Map.insert e1 (EdgeData {source=botPred,sink=topSucc}) (Map.delete e2 edgeInfo)
          )

        (Clear (Inner v), CoveredInFog) ->
          ( newTop
          , newBot
          , Map.adjust (\vd -> vd { outgoing = setAt e1 e1 topSucc (outgoing vd) }) v g
          , Map.insert e1 (EdgeData {source=botPred, sink=topSucc}) (Map.delete e2 edgeInfo)
          )


        (Clear (Inner v), Clear (Inner v')) ->
          ( newTop
          , newBot
          , Map.adjust (\vd -> vd { outgoing = setAt e1 e1 topSucc (outgoing vd) }) v $
              Map.adjust (\vd -> vd { incoming = setAt e2 e1 botPred (incoming vd) }) v' g
          , Map.insert e1 (EdgeData {source=botPred,sink=topSucc}) (Map.delete e2 edgeInfo)
          )
      )
      (top ng1, bottom ng2, Map.union (digraph ng1) (digraph ng2), Map.union (edges ng1) (edges ng2))
      partners

  toRow nl = 
    case nl of
      NoFogged w ->
        map (first Clear) $ Word.toList (bimap discardLabel discardLabel w)

      WithFogged pre w ->
        map (first Clear . discardLabel) pre
        ++ map (CoveredInFog,) (Word.toList (bimap fst fst w))

  partners = zip (toRow (bottom ng1)) (toRow (top ng2))

  -- setAt :: EdgeID -> EdgeID -> Foggy (OrBoundary Vertex) -> NeighborList (EdgeID, f) (EdgeID, o) -> NeighborList (EdgeID, f) (EdgeID, o)
  setAt e e_new fbv nl =
    case fbv of
      -- TODO: Inefficient. Fix to not traverse whole list if not necessary
      Clear ob ->
        case nl of
          WithFogged unfogged w ->
            WithFogged (map replace unfogged) w

          NoFogged w ->
            NoFogged (bimap replace replace w)
        where
        replace d@(_,(e',f)) = if e' == e then (ob, (e_new,f)) else d

      CoveredInFog ->
        case nl of
          WithFogged unfogged w ->
            -- Doing the exact same thing in both cases. Consider unifying.
            case List.break (\(_, (e',_)) -> e' == e) unfogged of
              (pre, []) -> -- already fogged
                bimap replace replace nl

              (pre, post) ->
                WithFogged pre (bimap replace replace (Word (map snd post) Nothing <> w))

          NoFogged (Word fs mo) ->
            -- These two cases are the same as well
            case List.break (\(_, (e',_)) -> e' == e) fs of
              (pre, []) ->
                case mo of
                  Nothing ->
                    nl -- error "Search.Graph.setAt: Inconsistent state: Got Nothing"

                  Just (_bv,(e',o)) ->
                    if e /= e'
                    then bimap replace replace nl -- error "Search.Graph.setAt: Inconsistent state: e /= e'"
                    else WithFogged fs (Word [] (Just (e_new, o)))

              (pre, post) ->
                WithFogged pre (Word (fmap (replace . snd) post) (fmap (replace . snd) mo))

          where
          replace d@(e',x) = if e' == e then (e_new, x) else d
        {-
        case fogAt e nl of
          WithFogged unfogged w -> WithFogged unfogged (bimap replace replace w)

          NoFogged w -> NoFogged w -}

      

-- TODO: Convert real Haskell programs into lists of moves
-- TODO: Analyze program graphs

graphsOfSizeAtMost' 
  :: (Hashable f, Ord f, Hashable o, Ord o, Show o, Show f) -- TODO: Debug 
  => [Trans f o]
  -> Int
  -> Word f o
  -> Word f o
  -> [] (NaturalGraph f o)
graphsOfSizeAtMost' tsList n start end =
  HashSet.toList
  $ HashSet.fromList (map moveListToGraph (moveSequencesOfSizeAtMost tsList n start end))


moveSequencesOfSizeAtMost tsList n start end = go start n
  where
  ts = HashMap.fromListWith (++) (map (\t -> (from t, [t])) tsList)

  go b k =
    if k == 0
    then
        if b == end then [[]] else []
    else
      concatMap (\(b', m) ->
        map (m:) (go b' (k - 1)))
      (branchOut ts b)

moveListToGraph = \case
  []   -> NaturalGraph mempty mempty Map.empty Map.empty Set.empty 0 0
  m:ms -> go (moveToGraph m) ms
  where
  go !acc ms =
    case ms of
      [] -> canonicalize acc
      m:ms -> go (acc `sequence` moveToGraph m) ms

moveSequencesOfSizeAtMostMemoNotTooHoley' branchOut n start end = map fst . HashSet.toList $ runST $ do
  arr <- newSTArray (0, n) Map.empty
  go arr n start
  where 
  newSTArray :: (Int, Int) -> Map k v -> ST s (STArray s Int (Map k v))
  newSTArray = newArray

  numberOfHoles = snd

  -- TODO: This is wrong, should allow things to happen after reaching the
  -- end.
  go arr n b
    | b == end  = return (HashSet.singleton ([], 0))
    | n == 0    = return HashSet.empty
    | otherwise = do
      memo <- readArray arr n
      case Map.lookup b memo of
        Nothing -> do
          -- let (singSteps, nicerSteps) = List.partition (\(_,m) -> singTrans (moveTrans m)) (branchOut ts b)
          progs <- fmap (HashSet.filter ((< 3) . numberOfHoles) . HashSet.unions) . forM (branchOut b) $ \(b', move) ->
            fmap
              (HashSet.map (\(moves,holes) -> (move : moves, holes + numHoles (name (moveTrans move)))))
              (go arr (n - 1) b')
          let progs' = if b == end then HashSet.insert ([], 0) progs else progs
              memo' = Map.insert b progs' memo
          memo' `seq` writeArray arr n memo'
          return progs'

        Just ps -> return ps

moveSequencesOfSizeAtMostMemo' branchOut n start end = HashSet.toList $ runST $ do
  arr <- newSTArray (0, n) Map.empty
  go arr n start
  where 
  newSTArray :: (Int, Int) -> Map k v -> ST s (STArray s Int (Map k v))
  newSTArray = newArray

  -- TODO: This is wrong, should allow things to happen after reaching the
  -- end.
  go arr n b
    | b == end  = return (HashSet.singleton [])
    | n == 0    = return HashSet.empty
    | otherwise = do
      memo <- readArray arr n
      case Map.lookup b memo of
        Nothing -> do
          -- let (singSteps, nicerSteps) = List.partition (\(_,m) -> singTrans (moveTrans m)) (branchOut ts b)
          progs <- fmap HashSet.unions . forM (branchOut b) $ \(b', move) ->
            fmap (HashSet.map (move :)) (go arr (n - 1) b')
          let progs' = if b == end then HashSet.insert [] progs else progs
          writeArray arr n (Map.insert b progs' memo)
          return progs'

        Just ps -> return ps

moveSequencesOfSizeAtMostMemo
  :: (Hashable f, Ord f, Hashable o, Ord o)
  => [Trans f o]
  -> Int
  -> Word f o
  -> Word f o
  -> [[Move f o]]
moveSequencesOfSizeAtMostMemo tsList n start end = HashSet.toList $ runST $ do
  arr <- newSTArray (0, n) Map.empty
  go arr n start
  where 
  newSTArray :: (Int, Int) -> Map k v -> ST s (STArray s Int (Map k v))
  newSTArray = newArray

  ts = HashMap.fromListWith (++) (map (\t -> (from t, [t])) tsList)

  -- TODO: This is wrong, should allow things to happen after reaching the
  -- end.
  go arr n b
    | b == end  = return (HashSet.singleton [])
    | n == 0    = return HashSet.empty
    | otherwise = do
      memo <- readArray arr n
      case Map.lookup b memo of
        Nothing -> do
          -- let (singSteps, nicerSteps) = List.partition (\(_,m) -> singTrans (moveTrans m)) (branchOut ts b)
          progs <- fmap HashSet.unions . forM (branchOut ts b) $ \(b', move) ->
            fmap (HashSet.map (move :)) (go arr (n - 1) b')
          let progs' = if b == end then HashSet.insert [] progs else progs
          writeArray arr n (Map.insert b progs' memo)
          return progs'

        Just ps -> return ps

graphsOfSizeAtMostMemo'
  :: (Hashable f, Ord f, Hashable o, Ord o)
  => (Word f o -> [(Word f o, Move f o)])
  -> Int
  -> Word f o
  -> Word f o
  -> [NaturalGraph f o]
graphsOfSizeAtMostMemo' branchOut n start end = map deleteStrayVertices . HashSet.toList $ runST $ do
  arr <- newSTArray (0, n) Map.empty
  go arr n start
  where 
  newSTArray :: (Int, Int) -> Map k v -> ST s (STArray s Int (Map k v))
  newSTArray = newArray

  -- TODO: This is wrong, should allow things to happen after reaching the
  -- end.
  go arr n b
    | b == end  = return (HashSet.singleton (idGraph end))
    | n == 0    = return HashSet.empty
    | otherwise = do
      memo <- readArray arr n
      case Map.lookup b memo of
        Nothing -> do
          -- let (singSteps, nicerSteps) = List.partition (\(_,m) -> singTrans (moveTrans m)) (branchOut ts b)
          progs <- fmap HashSet.unions . forM (branchOut b) $ \(b', move) ->
            fmap (HashSet.map (obliterate . sequence (moveToGraph move))) (go arr (n - 1) b')
          let progs' = if b == end then HashSet.insert (idGraph end) progs else progs
              memo' = Map.insert b progs' memo
          memo' `seq` writeArray arr n memo'
          return progs'

        Just ps -> return ps

graphsOfSizeAtMost
  :: (Hashable f, Ord f, Hashable o, Ord o)
  => [Trans f o]
  -> Int
  -> Word f o
  -> Word f o
  -> [NaturalGraph f o]
graphsOfSizeAtMost tsList n start end = map deleteStrayVertices . HashSet.toList $ runST $ do
  arr <- newSTArray (0, n) Map.empty
  go arr n start
  where 
  newSTArray :: (Int, Int) -> Map k v -> ST s (STArray s Int (Map k v))
  newSTArray = newArray

  ts = HashMap.fromListWith (++) (map (\t -> (from t, [t])) tsList)

  -- TODO: This is wrong, should allow things to happen after reaching the
  -- end.
  go arr n b
    | b == end  = return (HashSet.singleton (idGraph end))
    | n == 0    = return HashSet.empty
    | otherwise = do
      memo <- readArray arr n
      case Map.lookup b memo of
        Nothing -> do
          -- let (singSteps, nicerSteps) = List.partition (\(_,m) -> singTrans (moveTrans m)) (branchOut ts b)
          progs <- fmap HashSet.unions . forM (branchOut ts b) $ \(b', move) ->
            fmap (HashSet.map (obliterate . sequence (moveToGraph move))) (go arr (n - 1) b')
          let progs' = if b == end then HashSet.insert (idGraph end) progs else progs
          writeArray arr n (Map.insert b progs' memo)
          return progs'

        Just ps -> return ps

--  singTrans t = from t == mempty

-- Search with heuristics
graphsOfSizeAtMostH
  :: (Hashable f, Ord f, Hashable o, Ord o
  , Show f, Show o) -- TODO debug
  => [Trans f o] -> Int -> Word f o -> Word f o
  -> [NaturalGraph f o]
graphsOfSizeAtMostH tsList n start end = map deleteStrayVertices . HashSet.toList $ runST $ do
  arr <- newSTArray (0, n) Map.empty
  fmap HashSet.unions . forM (branchOut ts start) $ \(b', move) ->
    let g = moveToGraph move in
    fmap (HashSet.map (sequence g)) (go arr (n - 1) b' (moveTrans move))
  where 
  newSTArray :: (Int, Int) -> Map k v -> ST s (STArray s Int (Map k v))
  newSTArray = newArray

  ts = HashMap.fromListWith (++) (map (\t -> (from t, [t])) tsList)

  -- TODO: Some work is definitely duplicated.
  -- E.g., I start with AB, which gets rewritten to CB, to BC, to ABC, to
  -- AB, I shouldn't keep going since happens next should have been done up
  -- the call stack (or is about to be done).
  -- For each S, n store programs of length n which map out of S (to T), keyed by T
  go _   0 b _ = return $ if b == end then HashSet.singleton (idGraph end) else HashSet.empty
  go arr n b t = do
    memo <- readArray arr n
    case Map.lookup b memo of
      Nothing ->
        if Word.length b > 5
        then return HashSet.empty
        else do
          readArray arr n
          progs <- fmap HashSet.unions . forM (branchOut ts b) $ \(b', move) ->
            let t' = moveTrans move in
            if Word.length (from t) == 0 && Word.length (from t) == 0 -- from t == [] && from t' == []
            then return HashSet.empty
            else
              let g = moveToGraph move in
              fmap (HashSet.map (sequence g)) (go arr (n - 1) b' t')

          let progs' = if b == end then HashSet.insert (idGraph end) progs else progs
          writeArray arr n (Map.insert b progs' memo)
          return progs'

      Just ps -> return ps

moveTrans :: Move f o -> Trans f o
moveTrans = \case
  End _ t -> t
  Middle _ t _ -> t

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

{-
-- toTerm :: NaturalGraph f o -> AnnotatedTerm
toTerm = toTerm' . compressPaths

-- Three cases:
-- There are incoming vertices
-- There are no incoming vertices but there are outgoing vertices
-- There are no 
-- there are no incoming vertices or outgoing vertices.

-- TODO: Would be nice to have a "scratch pad" where I can write bits of
-- expressions to see their types
-- toTerm' :: NaturalGraph f o -> /nnotatedTerm
toTerm' ng0  trace ("YO: " ++ show ng0) (Map.minViewWithKey g) of
    Nothing ->
      AnnotatedTerm Id 0

    _ ->
      case topGoodVertexOfType1 of
        Just (v,vd) -> finishUp v vd top' fmaplevel
          where
          ins = mapMaybe (fmap snd . killFoggy) $ NeighborList.toList (incoming vd)
          in_0 = head ins
          in_n = last ins
          (top', fmaplevel) = (pre <> outgoing vd <> post, NeighborList.length pre)
            where
            (pre, post) =
              case top ng of
                WithFogged unfogged w ->
                  let (prel, postl) = exciseList in_0 in_n unfogged
                  in
                  (NoFogged (Word prel Nothing), WithFogged postl w)

                NoFogged (Word fs m) ->
                  let (prel, postl) = exciseList in_0 in_n fs in
                  case m of
                    Nothing ->
                      (NoFogged (Word prel Nothing), NoFogged (Word postl Nothing))

                    Just (_,(e,_)) ->
                      if e == in_n
                      then
                        (NoFogged (Word prel Nothing), NoFogged (Word postl Nothing))
                      else
                        (NoFogged (Word prel Nothing), NoFogged (Word postl m))

        Nothing ->
          case topGoodVertexOfType2 of
            Nothing -> AnnotatedTerm Id 0
            -- me here is the rightmost inport edge left of v
            Just (me, v, vd) ->
              case me of
                Nothing ->
                  finishUp v vd top' fmaplevel
                  where
                  (top', fmaplevel) =
                    (NeighborList.juxtapose (outgoing vd) (top ng), 0)

                Just e_l ->
                  finishUp v vd top' fmaplevel
                  where
                  (top', fmaplevel) = (pre <> outgoing vd <> post, NeighborList.length pre) 
                    where
                    (pre, post) =
                      case top ng of
                        WithFogged unfogged w ->
                          -- TODO: Fix ugly code
                          let (left, rightmost : postl) = List.break (\(_,(e,_)) -> e == e_l) unfogged
                              prel = left ++ [rightmost]
                          in
                          (NoFogged (Word prel Nothing), WithFogged postl w)

                        NoFogged (Word fs m) ->
                          case m of
                            Nothing ->
                              let (left, rightmost : postl) = List.break (\(_,(e,_)) -> e == e_l) fs
                                  prel = left ++ [rightmost]
                              in
                              (NoFogged (Word prel Nothing) , NoFogged (Word postl Nothing))

                            Just (_, (e, _)) ->
                              if e == e_l
                              then (top ng, mempty)
                              else
                                let (left, rightmost : postl) = List.break (\(_,(e,_)) -> e == e_l) fs
                                    prel = left ++ [rightmost]
                                in
                                (NoFogged (Word prel Nothing), NoFogged (Word postl m))

      where
      exciseList in_0 in_n xs =
        let (prel, ys) = List.break (\(_,(e,_)) -> e == in_0) xs
            postl      = tail (dropWhile (\(_,(e,_)) -> e /= in_n) ys)
        in
        (prel, postl)
              

  where
  finishUp v vd top' fmaplevel =
    trace ("removing: " ++ show (v, vd)) $
    fmapped numStraights (toTerm' (canonicalize ng') <> fmapped fmaplevel (label vd) )
    where
    ng' =
      ng
      { top = top'
      , bottom =
          NeighborList.mapVertex rename (bottom ng)

      , digraph =
          Map.map (\vd ->
            vd { incoming = NeighborList.mapVertex rename (incoming vd) })
            (Map.delete v (digraph ng))

      , edges =
          Map.map (\(EdgeData source sink) ->
            EdgeData (fmap rename source) (fmap rename sink))
            (List.foldl' (flip Map.delete) (edges ng) deletedEdges)

      , constantEdges =
          List.foldl' (flip Set.delete) (constantEdges ng) deletedEdges
      }

    rename bv = if bv == Inner v then Boundary else bv

    deletedEdges = map snd $ NeighborList.toList (incoming vd)

  (numStraights, ng) = countAndDropFMapStraights ng0

  g = digraph ng

  countAndDropFMapStraights ng_ =
    (numStraights, ng_ { top = dropStraights (top ng_), bottom = dropStraights (bottom ng_) })
    where
    numStraights =
      length $ takeWhile (\case {(Clear Boundary,_) -> True; _ -> False}) (NeighborList.toList (top ng0))

    -- dropStraights :: NeighborList f o -> NeighborList f o
    dropStraights = \case
      NoFogged (Word fs mo) ->
        NoFogged (Word (dropWhile isBoundary fs) (mfilter isBoundary mo))

      WithFogged pre w ->
        WithFogged (dropWhile isBoundary pre) w

      where
      isBoundary = \case {(Boundary,_) -> True; _ -> False}

  killFoggy (fbv,e) =
    case fbv of
      CoveredInFog -> Nothing
      Clear bv     -> Just (bv, e)

  -- topGoodVertexOfType1 :: Maybe (Vertex, VertexData f o)
  topGoodVertexOfType1 =
    findMap (\(v, vd) ->
      case mapMaybe killFoggy (NeighborList.toList (incoming vd)) of
        [] ->
          Nothing

        (Boundary,_e) : vs ->
          if all (\case {(Boundary,_) -> True; _ -> False}) vs
          then Just (v, vd)
          else Nothing

        _ -> Nothing)
      (Map.toList g)

  -- topGoodVertexOfType2 :: Maybe (Maybe EdgeID, Vertex, VertexData f o)
  topGoodVertexOfType2 =
    findMap (\(v, vd) ->
      case mapMaybe killFoggy (NeighborList.toList (incoming vd)) of
        [] ->
          let
            unblocked =
              List.filter (\(e_l, e_r) ->
                (o_1 `Set.member` lookupExn' "Graph:888" e_l rightnesses)
                && (e_r `Set.member` rightOfO_n))
                sameOriginPairs
              |> List.all (\(e_l, e_r) ->
                (e_l `Set.member` rightOfO_n)
                || o_1 `Set.member` lookupExn' "Graph:893" e_r rightnesses)
          in
          if unblocked
          then
            Just
            ( findMap (\(_,e) ->
                if o_1 `Set.member` lookupExn' "Graph:899" e rightnesses
                then Just e
                else Nothing)
                (reverse $ NeighborList.toList (top ng))
            , v
            , vd
            )
          else Nothing
          where
          -- assuming stray vertices have been deleted, it's safe to call
          -- head and last
          outlist = NeighborList.toList (outgoing vd)
          (_, o_1) = head outlist
          (_, o_n) = last outlist
          rightOfO_n = lookupExn' "Graph:913" o_n rightnesses

        _ ->
          Nothing
      )
      (Map.toList g)

  rightnesses = edgesRightOfAll ng

  sameOriginPairs =
    List.concatMap (\(_v, vd) ->
      List.concatMap (\case
        [] -> []
        (e1 : es) -> map (e1,) es)
      (List.tails (map snd $ NeighborList.toList (outgoing vd))))
    (Map.toList g)

  fmapped n (AnnotatedTerm f x) = case n of
    0 -> AnnotatedTerm f x
    1 -> AnnotatedTerm (Compound ("fmap " ++ wrapped)) x
    _ -> AnnotatedTerm (Compound (parens (List.intercalate " . " $ replicate n "fmap") ++ " " ++ wrapped)) x
    where
    wrapped = case f of { Simple x -> x; Compound x -> parens x; _ -> error "Search.Graph.fmapped: Impossible" }
    parens x = "(" ++ x ++ ")"
-}
{-
Want either
1. something that has only contiguous Boundary parents (resp children) and at least one of them.
  - easy to find and excise. Just map over all views of
    the incoming (resp outgoing) NeighborList

2. something with no parents (resp children) that has no obstacles on top (resp bottom) of it
    - can find such a thing by travelling first one down from a port, then
      right and up. Essentially attempting to make a vee.
    - By doing this, we will know the left boundary.


Suppose v has no incoming. Then u is an obstacle for v if there exist children of u
c1 (from edge e1) c2 (from edge e2) such that
  - e1 is left of the leftmost out edge of v
  - e2 is right of the rightmost out edge of v
  - c1 and v have a common descendant
  - c2 and v have a common descendant

We want to find v such that
  - v has no incoming
  - every edge that an outgoing edge of v is to the right of is either
    tendrilous or a port edge
We then want to find the rightmost port edge to the left of v

We want to find v such that
  - v has no incoming
  - for any two edges e_l, e_r such that e_l is to the left of edges of
    n
-}

{-
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

-- compressPaths :: NaturalGraph f o -> NaturalGraph f o
compressPaths ng = go ng startingVertices
  where
  startingVertices =
    filter (\(_v, vd) ->
      let inc = NeighborList.toList (incoming vd) in
      not (length inc == 1 && all (\case {(Clear (Inner _),_) -> True; _ -> False}) inc))
      (Map.toList (digraph ng))
    |> map fst

--  go :: Map Vertex (VertexData f o) -> [Vertex] -> Map Vertex (VertexData f o)
  go ng next =
    case next of
      [] -> ng
      v : next' ->
        let vs = slurpBackFrom v (digraph ng) in
        go (compressPath vs ng) next'

  slurpBackFrom v g =
    let vd@(VertexData { incoming }) = lookupExn' "Graph:1110" v g in
    case NeighborList.toList incoming of
      [(Clear (Inner v'), _)] ->
        (v, vd) : slurpBackFrom v' g

      _ ->
        [(v, vd)]

  compressPath path ng =
    let (v0, vd0) : _ = path
        (v1, vd1)     = last path
        lab           = mconcat (map (label . snd) path)
        (g', top')    =
          List.foldl' (\(g0,top0) (fbv, _e) ->
            case fbv of
              Clear Boundary -> (g0, replace v0 v1 top0)
              Clear (Inner v) -> (Map.adjust (\vd -> vd {outgoing=replace v0 v1 (outgoing vd)}) v g0, top0)
              CoveredInFog -> (g0,top0))

            ( Map.insert v0 (VertexData {label=lab,outgoing=outgoing vd0,incoming=incoming vd1})
                (digraph ng)
            , top ng
            )
            (NeighborList.toList (incoming vd1))
    in
    ng
    { top = top'
    , digraph = g'
    }
      
    
  replace v0 v1 nl =
    case nl of
      WithFogged pre w -> WithFogged (fmap f pre) w
      NoFogged w -> NoFogged (bimap f f w)
    where f = first (fmap (\v -> if v == v0 then v1 else v))
