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

import Control.Monad.State

import Search.Graph.Types.NeighborList (NeighborList(..))
import qualified Search.Types.Word as Word
import Search.Types.Word (Word(..))

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

-- If only I had quotient types...

Source -> Vertex with DummyVertex
Source -> Fog with DummyVertex
Source -> Sink with DummyVertex

Vertex -> Vertex with sourceIndex
Vertex -> Fog with sourceIndex
Vertex -> Sink with sourceIndex (or DummyVertex, or both)

Fog -> Fog
Fog -> Sink with DummyVertex
Fog -> Vertex with targetIndex

data OrTheSpecialVertex a = SpecialVertex | Regular a

type Source = OrTheSpecialVertex (Foggy Vertex)
type Sink   = OrTheSpecialVertex (Foggy Vertex)

data FogTarget
  = FogToFog
  | FogToRegular Int
  | FogToSink DummyVertex

data RegularTarget
  = RegularToFog Int
  | RegularToRegular Vertex Int
  | RegularToSink Int DummyVertex

data TopTarget
  = TopToFog DummyVertex
  | TopToRegular DummyVertex Int
  | TopToSink DummyVertex DummyVertex

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
  = Map Edge [Edge] -- sucessors. I.e., the set of things to the right of this edge

data WedgeKind = Vee | Caret -- actually not needed

data Wedge =
  Wedge
  { leftPath  :: [Edge]
  , rightPath :: [Edge]
  }

obliterateFrom :: NaturalGraph f o -> Edge -> NaturalGraph f o
obliterateFrom ng0 e =
  Set.foldl' (\ng e ->
    case e of
      Standard (StandardEdge {source, sink, sourceIndex}) ->
        case (source, sink) of
          (Source, ev') ->
            let incomingSuccs' = Map.insert sourceIndex CoveredInFog (incomingSuccs ng)
                ng'' = _
            in
            _
          (Sink, ev') -> _
          (Regular v, ev') -> _
          (Fog, ev') -> _ -- already obliterated

      FromFog ev i -> ng -- already obliterated
      ToFog ev i -> ng -- already obliterated
    )
    ng0 (edgesRightOf ng0 e)

  where
  fogSource :: ExplicitVert -> Int -> NaturalGraph f o -> NaturalGraph f o
  fogSource source sourceIndex ng = case source of
    Regular v ->
      ng { digraph = Map.adjust updateVertexData v (digraph ng) }

    Source ->
      ng { incomingSuccs = Map.insert sourceIndex CoveredInFog (incomingSuccs ng) }
      -- should actually fog out everything to the right of sourceIndex, but those things should be in the set as well
    Fog ->
      ng

    Sink -> error "fogSource: Got source = Sink"
    where
    updateVertexData :: VertexData f o -> VertexData f o
    updateVertexData vd = vd { outgoing = outgoing' }
      where
      outgoing' =
        case outgoing vd of
          WithFogged pre (Word fs mo) ->
            let (unfogged, fogged) = List.splitAt sourceIndex pre
            in
            WithFogged unfogged (Word (map snd fogged ++ fs) mo)

          NoFogged w ->
            _

  fogSink :: ExplicitVert -> ExplicitVert -> NaturalGraph f o -> NaturalGraph f o
  fogSink source sink ng =
    case sink of
      Regular v ->
        _

      Sink ->
        let i =
              case source of
                Regular v -> _
                Source -> _
                Sink -> _
                Fog -> _
        in
        ng { outgoingPreds = Map.insert i CoveredInFog (outgoingPreds ng) }

      Fog ->
        ng

      Source -> error "fogSink: Got sink = Source"


reachability :: RightnessGraph -> Map Edge (Set Edge)
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
          
edgesRightOf :: NaturalGraph f o -> Edge -> Set Edge
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

strictDescendants :: RightnessGraph -> Edge -> Set Edge
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

isRightOf :: RightnessGraph -> Edge -> Edge -> Bool
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
tendrils :: NaturalGraph f o -> (Set Edge, Set Edge)
tendrils ng = (topTendrils, botTendrils)
  where
  topTendrils = flip execState Set.empty $ do
    succs <- fmap catMaybes . forM (Map.toList (incomingSuccs ng)) $ \(i,fve) ->
      case fve of
        Clear ve -> return (Just (i,ve))
        CoveredInFog -> do
          modify (\s -> Set.insert (ToFog Source i) s)
          return Nothing

    topGoOnSuccs Source succs

  topGoOnSuccs ev0 enumedSuccs =
    fmap and $
      forM enumedSuccs $ \(i, suc) -> case suc of
        Dummy _ ->
          return False

        Real v -> topTendrilous v >>= \case
          True -> do
            modify (\s ->
              Set.insert
                (Standard
                  (StandardEdge {source=ev0, sink=Regular v, sourceIndex = i}))
                s)
            return True

          False -> return False

  topTendrilous :: Vertex -> State (Set Edge) Bool
  topTendrilous v0 = do
    succs <- getSuccs
    topGoOnSuccs (Regular v0) (zip [0..] succs)
    where
    getSuccs :: State (Set Edge) [Vert]
    getSuccs =
      case outgoing (lookupExn v0 g) of
        NoFogged w -> return . Word.toList $ bimap fst fst w
        WithFogged pre w -> do
          let n = length pre
              nw = Word.length w

          modify (\s0 -> List.foldl' (\s i -> Set.insert (ToFog (Regular v0) i) s) s0 [n..(n + nw - 1)])
          return (map fst pre)

  botTendrils = flip execState Set.empty $ do
    preds <- fmap catMaybes . forM (Map.toList (outgoingPreds ng)) $ \(dum, fve) ->
      case fve of
        Clear v -> return (Just v)
        CoveredInFog -> do
          modify (\s -> Set.insert (FromFog Sink dum) s)
          return Nothing

    botGoOnPreds Sink preds

  botGoOnPreds ev0 preds =
    fmap and $
      forM preds $ \case
        Dummy _ ->
          return False

        Real v -> botTendrilous v >>= \case
          True -> do
            modify (\s ->
              Set.insert
                (Standard
                  (StandardEdge {source=Regular v,sink=ev0,sourceIndex=findSourceIndex g ev0 v}))
              s)
            return True

          False ->
            return False


  botTendrilous :: Vertex -> State (Set Edge) Bool
  botTendrilous v0 = do
    preds <- getPreds
    botGoOnPreds (Regular v0) preds
    where
    getPreds :: State (Set Edge) [Vert]
    getPreds = 
      case incoming (lookupExn v0 g) of
        NoFogged w -> return . Word.toList $ bimap fst fst w
 
        WithFogged pre w -> do
          let n = length pre
              nw = Word.length w

          modify (\s0 -> List.foldl' (\s i -> Set.insert (FromFog (Regular v0) i) s) s0 [n..(n + nw - 1)])
          return (map fst pre)

  g = digraph ng

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

-- UTIL

lookupExn :: Ord k => k -> Map k a -> a
lookupExn k m = case Map.lookup k m of
  Just x -> x
  Nothing -> error "lookupExn: Lookup failed"


findSourceIndex g ev0 v =
  fromJust . List.findIndex (== ev0) . neighborListToExplicitVerts . outgoing $ lookupExn v g
  where

  neighborListToExplicitVerts :: NeighborList f o -> [ExplicitVert]
  neighborListToExplicitVerts = \case
    NoFogged w -> Word.toList $ bimap (vertToExplicitVert . fst) (vertToExplicitVert . fst) w
    WithFogged pre _w -> map (vertToExplicitVert . fst) pre

  vertToExplicitVert :: Vert -> ExplicitVert
  vertToExplicitVert = \case
    Dummy _ -> Sink
    Real r -> Regular r
