{-# LANGUAGE LambdaCase, ViewPatterns, TupleSections, NamedFieldPuns #-}
module Search.Graph.ToTerm where

import Search.Types
import Search.Graph.Types hiding (VertexData(..), NaturalGraph(..))
import qualified Search.Graph.Types.NeighborList as NeighborList
import Search.Graph.Types.NeighborList (NeighborList(..))
import Data.Monoid
import Data.Bifunctor
import qualified Data.List as List
import Data.Maybe
import Control.Applicative
import Search.Util
import qualified Search.Graph.Types as G
import qualified Search.Types.Word as Word

import qualified Data.Map as Map
import Data.Map (Map)

import Debug.Trace

data VertexData f = VertexData
  { label    :: TransName
  -- We store both the incoming and the outgoing vertices (in the proper
  -- order!) at every vertex to make traversal and obtaining the bimodal
  -- ordering easier. 
  , incoming :: [(Vert, f)]
  , outgoing :: [(Vert, f)]
  }
  deriving (Show, Eq)

data FreeNaturalGraph f =
  FreeNaturalGraph
  { incomingLabels :: [f]
  , incomingSuccs  :: Map DummyVertex Vert
  , incomingCount  :: Int

  , outgoingPreds  :: Map DummyVertex Vert
  , outgoingCount  :: Int

  , digraph        :: Map Vertex (VertexData f)
  }
  deriving (Show)

toTerm :: G.NaturalGraph f o -> AnnotatedTerm
toTerm = toTerm' . fromNaturalGraph

-- fromNaturalGraph :: G.NaturalGraph f o -> FreeNaturalGraph (Either f o)
fromNaturalGraph ng =
  -- traceShow ("yo", (botEdgesToDummy, ng)) $
  FreeNaturalGraph
  { incomingLabels = map (\(_,_,fo) -> fo) toplist
  , incomingSuccs  = boundaryMap topEdgesToDummy toplist
    
  , incomingCount  = length toplist
  , outgoingPreds  = boundaryMap botEdgesToDummy botlist
  , outgoingCount  = length botlist
  , digraph        = Map.map convertVertexData (G.digraph ng)
  }
  where
  convertVertexData :: G.VertexData (EdgeID, f) (EdgeID, o) -> VertexData (Either f o)
  convertVertexData (G.VertexData {G.label, G.incoming, G.outgoing}) =
    VertexData
    { label
    , incoming =
        mapMaybe
          (\(bv, e, fo) ->
            let
              ve =
                case bv of
                  Boundary ->
                    -- TODO This should really be lookupExn, not sure why
                    -- it was failing
                    Dummy <$> (Map.lookup e topEdgesToDummy)
                  Inner v ->
                    Just $ Real v
            in
            (, fo) <$> ve)
          (fromNeighborList incoming)

    , outgoing =
        mapMaybe
          (\(bv, e, fo) ->
            let
              ve =
                case bv of
                  Boundary ->
                    Dummy <$> (Map.lookup e botEdgesToDummy)
                  Inner v ->
                    Just $ Real v
            in
            (,fo) <$> ve)
          (fromNeighborList outgoing)
    }


  toplist = fromNeighborList (G.top ng)
  botlist = fromNeighborList (G.bottom ng)

  boundaryMap toDummies =
    Map.fromList .
      zipWith (\i (bv,e,_fo) ->
        let
          ve = 
            case bv of
              Boundary -> Dummy (lookupExn' "ToTerm:106" e toDummies)
              Inner v -> Real v
        in
        (i, ve))
        [0..]

  topEdgesToDummy :: Map EdgeID DummyVertex
  topEdgesToDummy =
    Map.fromList $ zipWith (\i (_bv,e,_) -> (e, i)) [0..] toplist

  botEdgesToDummy :: Map EdgeID DummyVertex
  botEdgesToDummy =
    Map.fromList $ zipWith (\i (_bv,e,_) -> (e, i)) [0..] botlist

  fromNeighborList :: NeighborList (EdgeID, f) (EdgeID, o) -> [(OrBoundary Vertex, EdgeID, Either f o)]
  fromNeighborList nl =
    case nl of
      WithFogged pre _w ->
        map (\(bv,(e,f)) -> (bv, e, Left f)) pre
      NoFogged (Word.Word fs mo) ->
        map (\(bv,(e,f)) -> (bv,e,Left f)) fs ++ maybe [] (\(bv,(e,o)) -> [(bv,e,Right o)]) mo


toTerm' :: FreeNaturalGraph f -> AnnotatedTerm
toTerm' ng0 = case findGoodVertex ng of
  Nothing -> mempty
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
      let (before, _) = Map.split leftStrands (incomingSuccs ng)
          (_, after)  = Map.split (leftStrands + dummiesRemoved - 1) (incomingSuccs ng)
      in
      (before, after)

    incomingSuccs' =
      Map.unions
      [ beforeSuccs
      , Map.fromList $ zipWith (\i (v,_) -> (i, v)) [leftStrands..] (outgoing vGoodData)
      , Map.mapKeysMonotonic (\k -> k + dummyShift) afterSuccs
      ]

    -- TODO: Merge this with g'
    outgoingPreds' =
      Map.foldWithKey (\d ve preds -> case ve of
        Dummy suc -> Map.adjust (\_ -> Dummy (d + dummyShift)) suc preds
        _         -> preds)
      (outgoingPreds ng)
      afterSuccs

    outgoingPreds'' =
      foldl (\m (i, (v, _)) -> case v of
        Dummy dum -> Map.adjust (\_ -> Dummy i) dum m
        _          -> m)
        outgoingPreds'
        (zip [leftStrands..] (outgoing vGoodData))

    g' =
      foldl (\digY'all r ->
        Map.adjust (\vd -> vd { incoming = map (first shift) (incoming vd) }) r digY'all)
        (Map.delete vGood g)
        (List.nub . mapMaybe (\case {Real r -> Just r; _ -> Nothing}) $ Map.elems afterSuccs)
      where
      shift ve = case ve of
        Dummy d -> if d >= leftStrands + dummiesRemoved then Dummy (d + dummyShift) else ve
        _       -> ve

    g'' =
      foldl (\digY'all (i, (v,_)) -> case v of
        Real r -> Map.adjust (updateIncomingAtFirst (Real vGood) (Dummy i)) r digY'all 
        _      -> digY'all)
        g'
        (zip [leftStrands..] (outgoing vGoodData))

    ng' = ng { incomingSuccs = incomingSuccs', digraph = g'', outgoingPreds = outgoingPreds'' }

    goodProgram = makeTopGoodProgram vGoodData

  Just (Bottom, (leftStrands, vGood, vGoodData)) ->
    case toTerm' ng' of
      (unannotatedTerm -> Id) -> fmapped (k + leftStrands) goodProgram -- I think n will always be 0 in this case
      p  -> fmapped k (fmapped leftStrands goodProgram <> p)
    where
    dummiesCreated = length $ incoming vGoodData
    dummiesRemoved = length . filter (\case {(Dummy _,_) -> True; _ -> False}) $ outgoing vGoodData
    dummyShift     = dummiesCreated - dummiesRemoved

    (beforePreds, afterPreds) =
      let (before, _) = Map.split leftStrands (outgoingPreds ng)
          (_, after)  = Map.split (leftStrands + dummiesRemoved - 1) (outgoingPreds ng)
      in
      (before, after)

    outgoingPreds' =
      Map.unions
      [ beforePreds
      , Map.fromList $ zipWith (\i (v,_) -> (i, v)) [leftStrands..] (incoming vGoodData)
      , Map.mapKeysMonotonic (\k -> k + dummyShift) afterPreds
      ]

    incomingSuccs' =
      Map.foldWithKey (\d ve succs -> case ve of
        Dummy pred -> Map.adjust (\_ -> Dummy (d + dummyShift)) pred succs
        _          -> succs)
        (incomingSuccs ng)
        afterPreds

    -- TODO: This and g' should sort of be done in one pass.
    incomingSuccs'' =
      foldl (\m (i, (v, _)) -> case v of
        Dummy dum -> Map.adjust (\_ -> Dummy i) dum m
        _         -> m)
      incomingSuccs'
      (zip [leftStrands..] (incoming vGoodData))

    g' =
      foldl (\digY'all r ->
        Map.adjust (\vd -> vd { outgoing = map (first shift) (outgoing vd) }) r digY'all)
        (Map.delete vGood g)
        (List.nub . mapMaybe (\case {Real r -> Just r; _ -> Nothing}) $ Map.elems afterPreds)
      where
      shift ve = case ve of
        Dummy d -> if d >= leftStrands + dummiesRemoved then Dummy (d + dummyShift) else ve
        _       -> ve

    g'' =
      foldl (\digY'all (i, (v, _)) -> case v of
        Real r -> Map.adjust (updateOutgoingAtFirst (Real vGood) (Dummy i)) r digY'all
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
    if Map.size start == 0
    then Nothing
    else foldr (\(d, ve) keepGoing -> case ve of
      Real r -> go d r <|> keepGoing
      Dummy _ -> keepGoing)
      Nothing
      (Map.toAscList start)
    where
    scanAcross _d []           = Nothing
    scanAcross d ((ve,_) : vs) = case ve of
      Real r   -> Just (d, r)
      Dummy d' -> scanAcross (max d d') vs -- I think d' always wins. I.e., d' == max d d'

    -- d is the number of strands strictly to the left of us
    go d r =
      let vd = lookupExn' "ToTerm:315" r g in
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
      []             -> mempty
      (Dummy _ : vs) -> let AnnotatedTerm t x w = loop vs in case t of
        Id         -> AnnotatedTerm Id x w 
        Simple s   -> AnnotatedTerm (Compound ("fmap (" ++ s ++ ")")) x w
        Compound s -> AnnotatedTerm (Compound ("fmap (" ++ s ++ ")")) x w

      (Real r : vs)  -> label (lookupExn' "ToTerm:337" r g) <> loop vs

  -- All children of the given vertex are dummys or childless
  makeBottomGoodProgram vd = loop (map fst (outgoing vd)) <> label vd where
    loop = \case
      []             -> mempty

      (Dummy _ : vs) -> let AnnotatedTerm t x w = loop vs in case t of
        Id         -> AnnotatedTerm Id x w
        Simple s   -> AnnotatedTerm (Compound ("fmap (" ++ s ++ ")")) x w
        Compound s -> AnnotatedTerm (Compound ("fmap (" ++ s ++ ")")) x w

      (Real r : vs) -> loop vs <> label (lookupExn' "ToTerm:349" r g)

fmapped n (AnnotatedTerm f x w) = case n of
  0 -> AnnotatedTerm f x w
  1 -> AnnotatedTerm (Compound ("fmap " ++ wrapped)) x w
  _ -> AnnotatedTerm (Compound (parens (List.intercalate " . " $ replicate n "fmap") ++ " " ++ wrapped)) x w
  where
  wrapped = case f of { Simple x -> x; Compound x -> parens x; _ -> error "Search.Graph.fmapped: Impossible" }
  parens x = "(" ++ x ++ ")"

-- Maintaining the invariant that the dummys are labelled 0..n
dropComponentStraights ng =
  let numComponentStraights =
        length $ takeWhile (\((_dumIn, inSucc), (dumOut, outPred)) -> case (inSucc, outPred) of
          (Dummy dumOut', Dummy _dumIn') -> dumOut' == dumOut
          _ -> False)
          (zip (Map.toDescList (incomingSuccs ng)) (Map.toDescList (outgoingPreds ng)))

      incoming' = Map.fromList . zip [0..] . map snd . reverse . drop numComponentStraights $ Map.toDescList (incomingSuccs ng)
      outgoing' = Map.fromList . zip [0..] . map snd . reverse . drop numComponentStraights $ Map.toDescList (outgoingPreds ng)
  in
  ng { incomingSuccs = incoming', outgoingPreds = outgoing' }

countAndDropFMapStraights :: FreeNaturalGraph f -> (Int, FreeNaturalGraph f)
countAndDropFMapStraights ng =
  let numFMapStraights =
        length $ takeWhile (\((_dumIn, inSucc), (dumOut, outPred)) -> case (inSucc, outPred) of
          (Dummy dumOut', Dummy _dumIn') -> dumOut' == dumOut
          _ -> False)
          (zip (Map.toAscList (incomingSuccs ng)) (Map.toAscList (outgoingPreds ng)))

      incoming' = Map.fromList . zip [0..] . map snd . drop numFMapStraights $ Map.toAscList (incomingSuccs ng)
      outgoing' = Map.fromList . zip [0..] . map snd . drop numFMapStraights $ Map.toAscList (outgoingPreds ng)

      shift = first $ \ve -> case ve of
        Dummy d -> Dummy (d - numFMapStraights)
        _       -> ve

      g' = Map.map (\vd -> vd { incoming = map shift (incoming vd), outgoing = map shift (outgoing vd) }) (digraph ng)
  in
  ( numFMapStraights
  , ng { incomingSuccs = incoming', outgoingPreds = outgoing', digraph = g' }
  )

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
leftFromRight (_ : _) [] = Nothing
leftFromRight (x : xs) (y : ys)
  | x == y    = leftFromRight xs ys
  | otherwise = Nothing
leftFromRight [] ys = Just ys

