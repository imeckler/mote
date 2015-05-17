{-# LANGUAGE LambdaCase, NamedFieldPuns, BangPatterns #-}
module Search.Graph.Canonicalize where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Search.Graph.Types
import qualified Data.List as List
import Data.Bifunctor
import Data.Maybe
import Data.Monoid

import Control.Monad.State

import Search.Graph.Types.NeighborList (NeighborList(..))
import qualified Search.Types.Word as Word
import Search.Types.Word (Word(..))
import Search.Util -- (lastMay, headMay)

{-
data ExplicitVert
  = Regular Vertex
  | Source
  | Sink
  | Fog
  deriving (Eq, Ord, Show)

data StandardEdge =
  StandardEdge
  { source :: Vertex
  , sink :: Vertex
  , sourceIndex :: Int -- the index of this edge in the ordering on the outgoing edges from the source
  }
  deriving (Eq, Ord, Show)
 -}
data FogTarget
  = FogToFog
  | FogToRegular Vertex Int
  | FogToSink DummyVertex
  deriving (Eq, Ord, Show)

data RegularTarget
  = RegularToFog Vertex Int
  | RegularToRegular Vertex Int -- source, source index
  | RegularToSink Int DummyVertex
  deriving (Eq, Ord, Show)

data TopTarget
  = TopToFog DummyVertex
  | TopToRegular DummyVertex Int
  | TopToSink DummyVertex DummyVertex
  deriving (Eq, Ord, Show)

-- If only I had quotient types...
data Edge
  = FromTop TopTarget
  | FromRegular RegularTarget
  | FromFog FogTarget
  deriving (Eq, Ord, Show)

{-
data Edge
  = Standard StandardEdge
  | FromFog ExplicitVert Int -- (target, index in the ordering of the incoming edges of the target) (perhaps should be the index in the incoming voided edges instead)
  | ToFog ExplicitVert Int -- (source, index in the ordering of the outgoing edges of the target)

  | FromSource DummyVertex (Foggy Vert)
  | ToSink DummyVertex (Foggy Vert)
  deriving (Eq, Ord, Show)
-}

-- Edge is the type of vertices of this graph
type RightnessGraph
  = Map EdgeID [EdgeID] -- sucessors. I.e., the set of things to the right of this edge

data WedgeKind = Vee | Caret -- actually not needed

data Wedge =
  Wedge
  { leftPath  :: [EdgeID]
  , rightPath :: [EdgeID]
  }

obliterateFrom :: NaturalGraph f o -> EdgeID -> NaturalGraph f o
obliterateFrom ng0 e0 =
  Set.foldl' (\ng e ->
    let EdgeData {source, sink} = lookupExn e edgeInfo
    in
    fogSource e source (fogSink e sink ng))
    ng0
    (edgesRightOf ng0 e0)

  where
  edgeInfo = edges ng0

  fogSource :: EdgeID -> OrBoundary (Foggy Vertex) -> NaturalGraph f o -> NaturalGraph f o
  fogSource e source ng =
    case source of
      Boundary ->
        ng { top = fogAt e (top ng) }

      Inner (Clear v) ->
        ng { digraph = Map.adjust (\vd -> vd { outgoing = fogAt e (outgoing vd) }) v (digraph ng) }

      Inner CoveredInFog ->
        ng

  fogSink :: EdgeID -> OrBoundary (Foggy Vertex) -> NaturalGraph f o -> NaturalGraph f o
  fogSink e sink ng =
    case sink of
      Boundary ->
        ng { bottom = fogAt e (bottom ng) }

      Inner (Clear v) ->
        ng { digraph = Map.adjust (\vd -> vd { incoming = fogAt e (incoming vd) }) v (digraph ng) }

      Inner CoveredInFog ->
        ng


fogAt :: EdgeID -> NeighborList (EdgeID, f) (EdgeID, o) -> NeighborList (EdgeID, f) (EdgeID, o)
fogAt = \e ns ->
  case ns of
    WithFogged fs w ->
      case splitAt (\(_, (e',_)) -> e == e') fs of
        Just (pre, fogged) ->
          WithFogged pre (Word (map snd fogged) Nothing <> w)

        Nothing -> ns

    NoFogged (Word fs mo) ->
      case splitAt (\(_, (e',_)) -> e == e') fs of
        Just (pre, fogged) ->
          WithFogged pre (Word (map snd fogged) (fmap snd mo))

        Nothing ->
          case mo of
            Nothing ->
              error "Search.Graph.Canonicalize.fogAt: inconsistent state. Got Nothing"

            Just (bv, (e',o)) ->
              if e /= e'
              then error "Search.Graph.Canonicalize.fogAt: inconsistent state. e /= e'"
              else WithFogged [] (Word (map snd fs) (Just (e', o)))

  where
  splitAt p xs = case xs of
    [] -> Nothing
    x : xs' -> if p x then Just ([], xs) else fmap (\(pre,ys) -> (x:pre,ys)) (splitAt p xs)


reachability :: RightnessGraph -> Map EdgeID (Set EdgeID)
reachability = goTop Map.empty
  where
  goTop acc !rg = 
    case Map.minViewWithKey rg of
      Just ((e, _es), rg') ->
        -- TODO inefficient for easiness
        let (acc',_) = go acc e in
        goTop acc' (Map.difference rg' acc')

      Nothing ->
        acc

    where
    go !acc0 e =
      case Map.lookup e acc0 of
        Just descs ->
          (acc0, descs)

        Nothing ->
          let children = lookupExn e rg
              (acc1, childrens'Descendants) =
                List.foldl (\(acc,cds) e' ->
                  let (acc',ds) = go acc e' 
                  in (acc', ds : cds))
                  (acc0, [])
                  children

              descs = List.foldl' (flip Set.insert) (Set.unions childrens'Descendants) children
          in
          (Map.insert e descs acc1, descs)

edgesRightOf :: NaturalGraph f o -> EdgeID -> Set EdgeID
edgesRightOf ng e
  | e `Set.member` topTendrils =
  -- If e is a top tendril and e' is a bottom tendril such that e is not
  -- diamond-right of e', then e' is right of e
    Set.union eDiamondRights
      (Set.filter
        (\e' -> not . Set.member e $ lookupExn e' diamondRightness)
        botTendrils)

  -- Similarly if e is a bottom tendril.
  | e `Set.member` botTendrils =
    Set.union eDiamondRights
      (Set.filter
        (\e' -> not . Set.member e $ lookupExn e' diamondRightness)
        topTendrils)

  | otherwise = eDiamondRights

  where
  eDiamondRights = lookupExn e diamondRightness
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
        else dfs (Set.insert e seen) (lookupExn e rg ++ next')

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
        else dfs (Set.insert e seen) (lookupExn e rg ++ next')



diamondRightnessgraph :: NaturalGraph f o -> RightnessGraph
diamondRightnessgraph ng =
  List.foldl' (\rg0 w ->
    List.foldl' (\rg1 e_l ->
      Map.insertWith (++) e_l (rightPath w) rg1)
      rg0
      (leftPath w))
    Map.empty
    wedges
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
      forM (fromNeighborList succs) $ \(fbv, e) ->
        case fbv of
          Clear (Inner v) ->
            go getNext (getNext (lookupExn v g)) >>= \case
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

wedges ng start nexts =
  concatMap wedgesFrom ((Boundary, start) : map (bimap Inner nexts) (Map.toList g))
  where
  -- TODO: I don't think I actually have to push back up for hanging
  -- local tendrils. It might be possible so consider that if this code
  -- doesn't work.

  makePath getNext = go
    where
    go = \case
      Clear (Inner v) -> 
        case (getNext . fromNeighborList . nexts $ lookupExn v g) of
          Just (v', e) ->
            (v', e) : go v'

          Nothing ->
            []

      _ -> []

  goingRight = makePath lastMay
  goingLeft = makePath headMay

  g = digraph ng

  wedgesFrom :: (OrBoundary Vertex, NeighborList (EdgeID, f) (EdgeID, o)) -> [Wedge]
  wedgesFrom (bv, nl) = zipWith wedgeFrom neighbs (tail neighbs)
    where
    neighbs = fromNeighborList nl
    wedgeFrom (fbv_l, e_l) (fbv_r, e_r) =
      Wedge {leftPath = map snd leftPath, rightPath = map snd rightPath}
      where
      leftPath0  = (fbv_l, e_l) : goingRight fbv_l
      rightPath0 = (fbv_r, e_r) : goingLeft fbv_r

      -- Find the first vertex that appears in both paths and cut the path
      -- off there. The first vertex that appears in both paths is the
      -- first vertex that appears in leftPath0 which also appears in
      -- rightPath0. Theta(n^2). Optimization opportunity.
      v_intersect = List.find (`List.elem` rightPath0) leftPath0

      (leftPath, rightPath) =
        case v_intersect of
          Just ve -> (takeTo ((== ve) . fst) leftPath0, takeTo ((== ve) . fst) rightPath0)
          Nothing -> (leftPath0, rightPath0)

vees :: NaturalGraph f o -> [Wedge]
vees ng = wedges ng (bottom ng) incoming

carets :: NaturalGraph f o -> [Wedge]
carets ng = wedges ng (top ng) outgoing


-- clean up
{-
componentOf :: Vertex -> 
componentOf v ng = _
  where
  go :: [OrBoundary
  go seen next0 =
    case next0 of
      [] -> seen
      (

componentOf v ng = go (Set.singleton v) [v] where
  go seen q0 =
    case q0 of
      []     -> seen
      ve : q ->
        case ve of
          UReal r ->
            let vd   = lookupExn r g
                next =
                  filter (not . (`Set.member` seen)) $
                    let disambig dir = disambiguate dir . fst
                    in
                    Word.toList (bimap (disambig In) (disambig In) (incoming vd))
                    ++ Word.toList (bimap (disambig Out) (disambig Out) (outgoing vd))
                    {-
                    map (\case { (Real r',_) -> UReal r'; (Dummy d,_) -> UDummy In d }) (incoming vd) 
                    ++ map (\case { (Real r',_) -> UReal r'; (Dummy d,_) -> UDummy Out d }) (outgoing vd) -}
                seen' = List.foldl' (flip Set.insert) seen next
            in
            go seen' (next ++ q)

          UDummy In d ->
            case lookupExn d inSuccs of
              CoveredInFog -> go seen q
              Clear ambigSuc ->
                let suc         = disambiguate Out ambigSuc
                    (q', seen') = if suc `Set.member` seen then (q, seen) else (suc : q, Set.insert suc seen)
                in
                go seen' q'

          UDummy Out d ->
            case lookupExn d outPreds of
              CoveredInFog -> go seen q
              Clear ambigPred ->
                let pred = disambiguate Out ambigPred
                    (q', seen') = if pred `Set.member` seen then (q, seen) else (pred : q, Set.insert pred seen)
                in
                go seen' q'

  inSuccs          = incomingSuccs ng
  outPreds         = outgoingPreds ng
  g                = digraph ng
  disambiguate dir = \case { Real r -> UReal r; Dummy d -> UDummy dir d }

-- Any stray vertex is reachable from a vertex that has no incoming edges.
deleteStrayVertices ng = ng { digraph = go g possibleStrays } where
  go acc remaining =
    case Map.minViewWithKey remaining of
      Nothing                     -> acc
      Just ((r, _vd), remaining') ->
        let comp = componentOf (UReal r) ng in
        if isStray comp
        then go (deleteFrom acc comp) (deleteFrom remaining' comp)
        else go acc (deleteFrom remaining' comp)
  possibleStrays = Map.filter (\vd -> Word.length (incoming vd) == 0) g
  g              = digraph ng
  isStray        = Set.foldl' (\x r -> case x of {UDummy {} -> False; _ -> r}) True 
  deleteFrom acc = Set.foldl' (\x h -> case x of {UReal r -> Map.delete r h; _ -> h}) acc

-}

deleteStrayVertices :: NaturalGraph f o -> NaturalGraph f o
deleteStrayVertices ng =
  ng
  { edges = Map.filter notStrayEdge (edges ng)
  , digraph = Set.foldl' (flip Map.delete) g nonStray  -- TODO: Use difference function
  , constantEdges = Set.filter notStrayEdge (constantEdges ng)
  }
  where
  nonStray = go Set.empty (map fst (fromNeighborList (top ng) ++ fromNeighborList (bottom ng)))

  notStrayEdge (EdgeData {source,sink}) =
    case (source, sink) of
      (Inner CoveredInFog, Inner CoveredInFog) -> False
      (Inner (Clear v), Inner (Clear v'))      -> (v `Set.member` nonStray) && (v' `Set.member` nonStray)
      (Boundary, _)                            -> True
      (_, Boundary)                            -> True

  go :: Set Vertex -> [Foggy (OrBoundary Vertex)] -> Set Vertex
  go seen next =
    case next of
      [] ->
        seen

      Clear (Inner v) : next' ->
        if v `Set.member` seen
        then go seen next'
        else
          let VertexData {incoming, outgoing} = lookupExn v g in
          go
            (Set.insert v seen)
            (map fst (fromNeighborList incoming ++ fromNeighborList outgoing) ++ next')

      CoveredInFog : next' ->
        go seen next'

      Clear Boundary : next' ->
        go seen next'

  g = digraph ng


-- UTIL

{-
lookupExn :: Ord k => k -> Map k a -> a
lookupExn k m = case Map.lookup k m of
  Just x -> x
  Nothing -> error "lookupExn: Lookup failed"


findSourceIndex g ev0 v =
  fromJust . List.findIndex (== ev0) . neighborListToExplicitVerts . outgoing $ lookupExn v g
-}

findIndex g inout ve0 v =
  fromJust . List.findIndex (== ve0) . neighborListToExplicitVerts . inout $ lookupExn v g

neighborListToExplicitVerts :: NeighborList f o -> [Vert]
neighborListToExplicitVerts = \case
  NoFogged w -> Word.toList $ bimap fst fst w
  WithFogged pre _w -> map fst pre

takeTo p = foldr (\x r -> if p x then [x] else x : r) []
  
fromNeighborList :: NeighborList (EdgeID, f) (EdgeID, o) -> [(Foggy (OrBoundary Vertex), EdgeID)]
fromNeighborList nl =
  case nl of
    WithFogged pre w ->
      map (\(bv, (e,_)) -> (Clear bv, e)) pre
      ++ Word.toList (bimap (\(e,_) -> (CoveredInFog, e)) (\(e,_) -> (CoveredInFog, e)) w)

    NoFogged w -> 
      let f (bv, (e,_)) = (Clear bv, e) in
      Word.toList (bimap f f w)
