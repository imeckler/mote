{-# LANGUAGE LambdaCase, NamedFieldPuns, BangPatterns, NoMonomorphismRestriction #-} -- TODO : mono
module Search.Graph.Canonicalize where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Search.Graph.Types
import qualified Data.List as List
import Data.Bifunctor
import Data.Monoid

import Control.Monad.State

import Search.Graph.Types.NeighborList (NeighborList(..))
import qualified Search.Graph.Types.NeighborList as NeighborList
import qualified Search.Types.Word as Word
import Search.Types.Word (Word(..))
import Search.Util -- (lastMay, headMay)

import Debug.Trace

-- EdgeID is the type of vertices of this graph
type RightnessGraph
  = Map EdgeID [EdgeID] -- sucessors. I.e., the set of things to the right of this edge

data WedgeKind = Vee | Caret -- actually not needed

data Wedge =
  Wedge
  { leftPath  :: [EdgeID]
  , rightPath :: [EdgeID]
  }
  deriving (Show)

-- canonicalize :: NaturalGraph f o -> NaturalGraph f o
canonicalize = deleteStrayVertices . obliterate -- . traceShowId

-- obliterate :: NaturalGraph f o -> NaturalGraph f o
obliterate ng0 = Set.foldl' obliterateFrom ng0 (constantEdges ng0)

-- There is at least one bug in this function. It produced the following
-- silly graph
-- NaturalGraph {top = NoFogged (Word [(Inner 1,(6,("[]","[]")))] (Just (Inner 0,(1,("Foo.Filepath","[]"))))), bottom = WithFogged [(Inner 1,(8,("GHC.Types.IO","[]"))),(Inner 1,(9,("[]","[]")))] (Word [] (Just (28,("GHC.Types.Int","[]")))), digraph = fromList [(0,VertexData {label = AnnotatedTerm {unannotatedTerm = Simple "readFileMay", numHoles = 0}, incoming = NoFogged (Word [] (Just (Boundary,(1,("Foo.Filepath","[]"))))), outgoing = NoFogged (Word [(Inner 1,(2,("GHC.Types.IO","[]"))),(Boundary,(3,("Data.Maybe.Maybe","[]"))),(Boundary,(4,("[]","[]")))] (Just (Boundary,(5,("GHC.Types.Char","[]")))))}),(1,VertexData {label = AnnotatedTerm {unannotatedTerm = Simple "sequenceA", numHoles = 0}, incoming = NoFogged (Word [(Boundary,(6,("[]","[]"))),(Inner 0,(2,("GHC.Types.IO","[]")))] Nothing), outgoing = NoFogged (Word [(Boundary,(8,("GHC.Types.IO","[]"))),(Boundary,(9,("[]","[]")))] Nothing)})], edges = fromList [(1,EdgeData {source = Clear Boundary, sink = Clear (Inner 0)}),(2,EdgeData {source = Clear (Inner 0), sink = Clear (Inner 1)}),(3,EdgeData {source = Clear (Inner 0), sink = Clear Boundary}),(4,EdgeData {source = Clear (Inner 0), sink = Clear Boundary}),(5,EdgeData {source = Clear (Inner 0), sink = Clear Boundary}),(6,EdgeData {source = Clear Boundary, sink = Clear (Inner 1)}),(8,EdgeData {source = Clear (Inner 1), sink = Clear Boundary}),(9,EdgeData {source = Clear (Inner 1), sink = Clear Boundary}),(27,EdgeData {source = CoveredInFog, sink = CoveredInFog}),(28,EdgeData {source = CoveredInFog, sink = Clear Boundary})], constantEdges = fromList [1,5,27,28], freshVertex = 4, freshEdgeID = 29}
-- obliterateFrom :: NaturalGraph f o -> EdgeID -> NaturalGraph f o
obliterateFrom ng0 e0 =
  Set.foldl' (\ng e ->
    let EdgeData {source, sink}
          = lookupExn' "can82" e edgeInfo
    in
    fogSource e source (fogSink e sink ng)
             )
    ng0
    (edgesRightOf ng0 e0)

  where
  edgeInfo = edges ng0

  -- fogSource :: EdgeID -> Foggy (OrBoundary Vertex) -> NaturalGraph f o -> NaturalGraph f o
  fogSource e source ng0 =
    let ng = ng0 { edges = Map.insert e (EdgeData {source=source,sink=CoveredInFog}) (edges ng0) }
    in
    case source of
      Clear Boundary ->
        ng { top = fogAt e e (top ng) }

      Clear (Inner v) ->
        ng { digraph = Map.adjust (\vd -> vd { outgoing = fogAt e e (outgoing vd) }) v (digraph ng) }

      CoveredInFog ->
        ng

  -- fogSink :: EdgeID -> Foggy (OrBoundary Vertex) -> NaturalGraph f o -> NaturalGraph f o
  fogSink e sink ng0 =
    case sink of
      Clear bv ->
        let e_new = freshEdgeID ng0
            ng =
              ng0
              { freshEdgeID = e_new + 1
              , edges = Map.insert e_new (EdgeData {source=CoveredInFog,sink=sink}) (edges ng0)
              , constantEdges =
                  if e `Set.member` constantEdges ng0
                  then Set.insert e_new (constantEdges ng0)
                  else constantEdges ng0
              }
        in
        case bv of
          Boundary ->
            ng { bottom = fogAt e e_new (bottom ng) }

          Inner v ->
            ng { digraph = Map.adjust (\vd -> vd { incoming = fogAt e e_new (incoming vd) }) v (digraph ng) }

      CoveredInFog ->
        ng0


-- fogAt :: EdgeID -> NeighborList (EdgeID, f) (EdgeID, o) -> NeighborList (EdgeID, f) (EdgeID, o)
-- TODO: This is a special case of Search.Graph.setAt. Unify them
fogAt e e_new nl =
  case nl of
    WithFogged unfogged w ->
      let (pre, post) = List.break (\(_bv,(e',_)) -> e' == e) unfogged in
      WithFogged pre (bimap replace replace (Word (map snd post) Nothing <> w ))

    NoFogged (Word fs mo) ->
      case List.break (\(_bv, (e',_)) -> e' == e) fs of
        (_pre, []) ->
          case mo of
            Nothing ->
              nl
              -- error "Search.Graph.Canonicalize.fogAt: Inconsistent state: Got Nothing"

            Just (_bv, (e', o)) ->
              if e /= e'
                 -- IDK if doing replace is even necessary
              then bimap replace replace nl   -- error "Search.Graph.Canonicalize.fogAt: Inconsistent state: e /= e'"
              else WithFogged fs (Word [] (Just (e_new, o)))

        (pre, post) ->
          WithFogged pre (bimap (replace . snd) (replace . snd) (Word post mo))

  where
  replace :: (EdgeID, a) -> (EdgeID, a)
  replace d@(e', x) = if e' == e then (e_new, x) else d
  {-
  case ns of
    WithFogged fs w ->
      case splitWhen (\(_, (e',_)) -> e == e') fs of
        Just (pre, fogged) ->
          WithFogged pre (Word (map snd fogged) Nothing <> w)

        Nothing -> ns

    NoFogged (Word fs mo) ->
      case splitWhen (\(_, (e',_)) -> e == e') fs of
        Just (pre, fogged) ->
          WithFogged pre (Word (map snd fogged) (fmap snd mo))

        Nothing ->
          case mo of
            Nothing ->
              error "Search.Graph.Canonicalize.fogAt: inconsistent state. Got Nothing"

            Just (_bv, (e',o)) ->
              if e /= e'
              then ns -- error "Search.Graph.Canonicalize.fogAt: inconsistent state. e /= e'"
              else WithFogged fs (Word [] (Just (e', o)))-- WithFogged [] (Word (map snd fs) (Just (e', o)))
-}
-- TODO: Replace with better algorithm
reachability :: RightnessGraph -> Map EdgeID (Set EdgeID)
reachability rg0 =
  Map.mapWithKey (\e sucs -> Set.delete e $ dfs (Set.singleton e) sucs) rg0
  where
  dfs seen next =
    case next of
      [] -> seen
      e : next' ->
        if e `Set.member` seen
        then dfs seen next'
        else dfs (Set.insert e seen) (lookupExn' "can 113" e rg0 ++ next')

edgesRightOfAll :: NaturalGraph f o -> Map EdgeID (Set EdgeID)
edgesRightOfAll ng =
  Map.mapWithKey (\e _ed -> makeRights e)
    (edges ng)
  where
  diamondRightness = reachability (diamondRightnessgraph ng)
  (topTendrils, botTendrils) = tendrils ng

  makeRights e
    | e `Set.member` topTendrils =
    -- If e is a top tendril and e' is a bottom tendril such that e is not
    -- diamond-right of e', then e' is right of e
      Set.union eDiamondRights
        (Set.filter
          (\e' -> not . Set.member e $ lookupExn' "can 187" e' diamondRightness)
          botTendrils)

    -- Similarly if e is a bottom tendril.
    | e `Set.member` botTendrils =
      Set.union eDiamondRights
        (Set.filter
          (\e' -> not . Set.member e $ lookupExn' "can 194" e' diamondRightness)
          topTendrils)

    | otherwise = eDiamondRights
    where
    eDiamondRights = lookupExn' "can 199" e diamondRightness

edgesRightOf :: NaturalGraph f o -> EdgeID -> Set EdgeID
edgesRightOf ng e
  | e `Set.member` topTendrils =
  -- If e is a top tendril and e' is a bottom tendril such that e is not
  -- diamond-right of e', then e' is right of e
    Set.union eDiamondRights
      (Set.filter
        (\e' -> not . Set.member e $ lookupExn' "can 208" e' diamondRightness)
        botTendrils)

  -- Similarly if e is a bottom tendril.
  | e `Set.member` botTendrils =
    Set.union eDiamondRights
      (Set.filter
        (\e' -> not . Set.member e $ lookupExn' "can 215" e' diamondRightness)
        topTendrils)

  | otherwise = eDiamondRights

  where
  eDiamondRights   = lookupExn' "can 211" e diamondRightness
  diamondRightness = reachability diamondGraph
  diamondGraph     = diamondRightnessgraph ng
  -- Rather wasteful to compute all the top and bottom tendrils
  -- when I really just need the bottom tendrils if e is a top tendril
  -- and the top tendrils if e is a bottom tendril
  (topTendrils, botTendrils) = tendrils ng

strictDescendants :: RightnessGraph -> EdgeID -> Set EdgeID
strictDescendants rg e0 = Set.delete e0 (dfs Set.empty [e0])
  where
  dfs !seen next =
    case next of
      [] ->
        seen

      e : next' ->
        if e `Set.member` seen
        then dfs seen next'
        else dfs (Set.insert e seen) (lookupExn' "can 240" e rg ++ next')

isRightOf :: RightnessGraph -> EdgeID -> EdgeID -> Bool
isRightOf rg e1 e2 = e1 /= e2 && dfs Set.empty [e1]
  where
  dfs !seen next =
    case next of
      [] -> False
      e : next' ->
        if e == e2
        then True
        else if e `Set.member` seen
        then dfs seen next'
        else dfs (Set.insert e seen) (lookupExn' "can 253" e rg ++ next')



diamondRightnessgraph :: NaturalGraph f o -> RightnessGraph
diamondRightnessgraph ng =
  let g0 = 
        List.foldl' (\rg0 w ->
          List.foldl' (\rg1 e_l ->
            Map.insertWith (++) e_l (rightPath w) rg1)
            rg0
            (leftPath w))
          Map.empty
          wedges
  in
  -- TODO: Check if this is faster than folding over all the edges
  Map.unionWith (\l _r -> l) g0 (Map.map (\_ -> []) (edges ng))
  where
  wedges = carets ng ++ vees ng

-- A bit inefficient to do this in a different stage from detecting carets
-- and vees, but it's asymptotically the same and makes things a lot
-- simpler.
-- Returns
-- (edges belonging to a from-top tendril, edges belonging to a from-bottom tendril)

tendrils :: NaturalGraph f o -> (Set EdgeID, Set EdgeID)
tendrils ng = (topTendrils, botTendrils)
  where
  topTendrils :: Set EdgeID
  topTendrils = flip execState Set.empty $ go outgoing (top ng)

  botTendrils :: Set EdgeID
  botTendrils = flip execState Set.empty $ go incoming (bottom ng)

  go getNext succs =
    fmap and $
      forM (NeighborList.toList succs) $ \(fbv, e) ->
        case fbv of
          Clear (Inner v) ->
            go getNext (getNext (lookupExn' "can 289" v g)) >>= \case
              True -> do
                modify (\s -> Set.insert e s)
                return True

              False ->
                return False

          Clear Boundary ->
            return False

          CoveredInFog -> do
            modify (\s -> Set.insert e s)
            return True



  g = digraph ng

vees :: NaturalGraph f o -> [Wedge]
vees ng = wedges (bottom ng) incoming outgoing ng

carets :: NaturalGraph f o -> [Wedge]
carets ng = wedges (top ng) outgoing incoming ng

wedges start forward backward ng =
  concatMap wedgesFrom ((Boundary, start) : map (bimap Inner forward) (Map.toList g))
  where
  -- TODO: I don't think I actually have to push back up for hanging
  -- local tendrils. It might be possible so consider that if this code
  -- doesn't work.
  makePath getNext = go
    where
    getNext' v e =
      let vd = lookupExn v g in
      case getNext (NeighborList.toList (forward vd)) of
        Nothing ->
          Nothing

        Just ve ->
          if Just e == fmap snd (getNext (NeighborList.toList (backward vd)))
          then Just ve
          else Nothing

    go (bv, e0) = case bv of
      Clear (Inner v) -> 
        case (getNext' v e0) of
          Just d ->
            d : go d

          Nothing ->
            []

      _ -> []



  goingRight = makePath lastMay
  goingLeft  = makePath headMay

  g = digraph ng

  wedgesFrom :: (OrBoundary Vertex, NeighborList (EdgeID, f) (EdgeID, o)) -> [Wedge]
  wedgesFrom (_bv, nl) = zipWith wedgeFrom neighbs (tail neighbs)
    where
    neighbs = NeighborList.toList nl

    wedgeFrom :: (Foggy (OrBoundary Vertex), EdgeID) -> (Foggy (OrBoundary Vertex), EdgeID) -> Wedge
    wedgeFrom d_l d_r =
      Wedge { leftPath = map snd leftPath, rightPath = map snd rightPath }
      where
      leftPath0 = d_l : goingRight d_l
      rightPath0 = d_r : goingLeft d_r

      -- Find the first vertex that appears in both paths and cut the path
      -- off there. The first vertex that appears in both paths is the
      -- first vertex that appears in leftPath0 which also appears in
      -- rightPath0. Theta(n^2). Optimization opportunity.
      v_intersect = List.find (\(ve, _) -> List.any ((== ve) . fst) rightPath0) leftPath0
      (leftPath, rightPath) =
        case v_intersect of
          Just (ve,_) ->
            (takeTo ((== ve) . fst) leftPath0, takeTo ((== ve) . fst) rightPath0)

          Nothing ->
            (leftPath0, rightPath0)

{-
vees :: NaturalGraph f o -> [Wedge]
vees ng =
  concatMap veesFrom ((Boundary, bottom ng) : map (bimap Inner incoming) (Map.toList g))
  where
  -- TODO: I don't think I actually have to push back up for hanging
  -- local tendrils. It might be possible so consider that if this code
  -- doesn't work.
  makePath getNext = go
    where
    getNext' v e =
      let vd = lookupExn v g in
      case getNext (NeighborList.toList (incoming vd)) of
        Nothing ->
          Nothing

        Just ve ->
          if Just e == fmap snd (getNext (NeighborList.toList (outgoing vd)))
          then Just ve
          else Nothing

    go (bv, e0) = case bv of
      Clear (Inner v) -> 
        case (getNext' v e0) of
          Just d ->
            d : go d

          Nothing ->
            []

      _ -> []



  goingRight = makePath lastMay
  goingLeft  = makePath headMay

  g = digraph ng

  veesFrom :: (OrBoundary Vertex, NeighborList (EdgeID, f) (EdgeID, o)) -> [Wedge]
  veesFrom (bv, nl) = zipWith veeFrom neighbs (tail neighbs)
    where
    neighbs = NeighborList.toList nl

    veeFrom :: (Foggy (OrBoundary Vertex), EdgeID) -> (Foggy (OrBoundary Vertex), EdgeID) -> Wedge
    veeFrom d_l d_r =
      Wedge { leftPath = map snd leftPath0, rightPath = map snd rightPath0 }
      where
      leftPath0 = d_l : goingRight d_l
      rightPath0 = d_r : goingLeft d_r

      -- Find the first vertex that appears in both paths and cut the path
      -- off there. The first vertex that appears in both paths is the
      -- first vertex that appears in leftPath0 which also appears in
      -- rightPath0. Theta(n^2). Optimization opportunity.
      v_intersect = List.find (\(ve, _) -> List.any ((== ve) . fst) rightPath0) leftPath0
      (leftPath, rightPath) =
        case v_intersect of
          Just (ve,_) ->
            (takeTo ((== ve) . fst) leftPath0, takeTo ((== ve) . fst) rightPath0)

          Nothing ->
            (leftPath0, rightPath0)
-}

-- clean up
deleteStrayVertices :: NaturalGraph f o -> NaturalGraph f o
deleteStrayVertices ng =
  ng
  { edges = edges'
  , digraph = Map.filterWithKey (\v _vd -> v `Set.member` nonStray) g
  -- TODO: Use intersection function
  , constantEdges =
      Set.filter (`Map.member` edges') (constantEdges ng)
  }
  where
  edges' = Map.filter notStrayEdge (edges ng)

  nonStray = go Set.empty (map fst (NeighborList.toList (top ng) ++ NeighborList.toList (bottom ng)))

  notStrayEdge (EdgeData {source,sink}) =
    case (source, sink) of
      (CoveredInFog, CoveredInFog)        -> False
      (Clear (Inner v), Clear (Inner v')) -> (v `Set.member` nonStray) && (v' `Set.member` nonStray)
      (Clear (Inner v), CoveredInFog)     -> v `Set.member` nonStray
      (CoveredInFog, Clear (Inner v))     -> v `Set.member` nonStray
      (Clear Boundary, _)                 -> True
      (_, Clear Boundary)                 -> True

  go :: Set Vertex -> [Foggy (OrBoundary Vertex)] -> Set Vertex
  go seen next =
    case next of
      [] ->
        seen

      Clear (Inner v) : next' ->
        if v `Set.member` seen
        then go seen next'
        else
          let VertexData {incoming, outgoing} = lookupExn' "can 469" v g in
          go
            (Set.insert v seen)
            (map fst (NeighborList.toList incoming ++ NeighborList.toList outgoing) ++ next')

      CoveredInFog : next' ->
        go seen next'

      Clear Boundary : next' ->
        go seen next'

  g = digraph ng


-- UTIL


takeTo p = foldr (\x r -> if p x then [x] else x : r) []
  
splitWhen p xs = case xs of
  [] -> Nothing
  x : xs' ->
    if p x
    then Just ([], xs)
    else fmap (\(pre,ys) -> (x:pre,ys)) (splitWhen p xs')


