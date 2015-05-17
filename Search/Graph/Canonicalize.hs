{-# LANGUAGE LambdaCase, NamedFieldPuns, BangPatterns #-}
module Canonicalize where

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


  fromNeighborList :: NeighborList (EdgeID, f) (EdgeID, o) -> [(Foggy (OrBoundary Vertex), EdgeID)]
  fromNeighborList nl =
    case nl of
      WithFogged pre w ->
        map (\(bv, (e,_)) -> (Clear bv, e)) pre
        ++ Word.toList (bimap (\(e,_) -> (CoveredInFog, e)) (\(e,_) -> (CoveredInFog, e)) w)

      NoFogged w -> 
        let f (bv, (e,_)) = (Clear bv, e) in
        Word.toList (bimap f f w)

  g = digraph ng

{-
tendrils :: NaturalGraph f o -> (Set Edge, Set Edge)
tendrils ng = (topTendrils, botTendrils)
  where
  topTendrils = flip execState Set.empty $ do
    succs <- fmap catMaybes . forM (Map.toList (incomingSuccs ng)) $ \(i,fve) ->
      case fve of
        Clear ve -> return (Just (i,ve))
        CoveredInFog -> do
          modify _ -- (\s -> Set.insert (ToFog Source i) s)
          return Nothing

    topGoOnSuccs
      (\dum v -> FromTop . TopToRegular dum $ findIndex g incoming (Dummy dum) v)
      succs
    where

  topGoOnSuccs mkEdge enumedSuccs =
    fmap and $
      forM enumedSuccs $ \(i, suc) -> case suc of
        Dummy _ ->
          return False

        Real v -> topTendrilous v >>= \case
          True -> do
            modify (\s ->
              Set.insert 
                (mkEdge i v)
              {-
                (Standard
                  (StandardEdge {source=ev0, sink=Regular v, sourceIndex = i})) -}
                s)
            return True

          False -> return False

  topTendrilous :: Vertex -> State (Set Edge) Bool
  topTendrilous v0 = do
    succs <- getSuccs
    topGoOnSuccs
      (\i v -> FromRegular $ RegularToRegular v i)
      (zip [0..] succs)
    where
    getSuccs :: State (Set Edge) [Vert]
    getSuccs =
      case outgoing (lookupExn v0 g) of
        NoFogged w -> return . Word.toList $ bimap fst fst w
        WithFogged pre w -> do
          let n = length pre
              nw = Word.length w

          modify (\s0 ->
            List.foldl' (\s i ->
              Set.insert (FromRegular $ RegularToFog v0 i) s)
              s0
              [n..(n + nw - 1)])

          return (map fst pre)

  botTendrils = flip execState Set.empty $ do
    preds <- fmap catMaybes . forM (Map.toList (outgoingPreds ng)) $ \(dum, fve) ->
      case fve of
        Clear v -> return (Just (dum, v))
        CoveredInFog -> do
          modify (\s -> Set.insert (FromFog $ FogToSink dum) s) -- Set.insert (FromFog Sink dum) s)
          return Nothing

    botGoOnPreds
      (\dum v -> FromRegular $ RegularToSink dum (findIndex g outgoing (Dummy dum) v)
      preds

  botGoOnPreds mkEdge enumedPreds =
    fmap and $
      forM enumedPreds $ \(i,v) -> case v of
        Dummy _ ->
          return False

        Real v -> botTendrilous v >>= \case
          True -> do
            modify (\s ->
              Set.insert
                (mkEdge i v)
                {- (Standard
                  (StandardEdge {source=Regular v,sink=ev0,sourceIndex=findSourceIndex g ev0 v})) -}
              s)
            return True

          False ->
            return False


  botTendrilous :: Vertex -> State (Set Edge) Bool
  botTendrilous v0 = do
    preds <- getPreds
    botGoOnPreds
      (\i v -> FromRegular $ RegularToRegular v _) -- shiz
--      (Regular v0) 
      (zip [0..] preds)
    where
    getPreds :: State (Set Edge) [Vert]
    getPreds = 
      case incoming (lookupExn v0 g) of
        NoFogged w ->
          return . Word.toList $ bimap fst fst w
 
        WithFogged pre w -> do
          let n = length pre
              nw = Word.length w

          modify (\s0 ->
            List.foldl' (\s i ->
              Set.insert (FromFog $ FogToRegular v0 i) s)
              s0
              [n..(n + nw - 1)])

          return (map fst pre)

  g = digraph ng
-}
vees :: NaturalGraph f o -> [Wedge]
vees = _
  where {-
  -- \/
  startFrom :: ExplicitVert -> ExplicitVert -> ExplicitVert -> Wedge
  startFrom nadir l r = _ $ go l r (Map.empty, Map.empty)
    where
    -- stop when you hit a vertex that has an edge in of you that goes the
    -- wrong way.
    go
      :: Int
      -> Maybe ExplicitVert -> Maybe ExplicitVert
      -> State (Map ExplicitVert Int, Map ExplicitVert Int) () -- gives the order of the vertices in each path
    go i ml mr = case (ml, mr) of
      (Just l, Just r) -> _
-}

carets :: NaturalGraph f o -> [Wedge]
carets = _

-- clean up

{-
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
-- UTIL

lookupExn :: Ord k => k -> Map k a -> a
lookupExn k m = case Map.lookup k m of
  Just x -> x
  Nothing -> error "lookupExn: Lookup failed"


{-
findSourceIndex g ev0 v =
  fromJust . List.findIndex (== ev0) . neighborListToExplicitVerts . outgoing $ lookupExn v g
-}

findIndex g inout ve0 v =
  fromJust . List.findIndex (== ve0) . neighborListToExplicitVerts . inout $ lookupExn v g

neighborListToExplicitVerts :: NeighborList f o -> [Vert]
neighborListToExplicitVerts = \case
  NoFogged w -> Word.toList $ bimap fst fst w
  WithFogged pre _w -> map fst pre

