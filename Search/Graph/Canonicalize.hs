{-# LANGUAGE LambdaCase, NamedFieldPuns #-}
module Canonicalize where

import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Search.Graph.Types
import qualified Data.List as List
import Search.Util

import Control.Monad.State
import Control.Monad.Error

data ExplicitVert
  = Regular Vertex
  | Source
  | Sink
  deriving (Eq, Ord, Show)

data Edge =
  Edge
  { source :: ExplicitVert
  , sink :: ExplicitVert
  , sourceIndex :: Int -- the index of this edge in the ordering on the outgoing edges from the source
  }

-- Edge is the type of vertices of this graph
type RightnessGraph
  = Map Edge (Set Edge) -- sucessors. I.e., the set of things to the right of this edge

data WedgeKind = Vee | Caret -- actually not needed

data Wedge =
  Wedge
  { leftPath  :: [Edge]
  , rightPath :: [Edge]
  }

rightnessGraph :: NaturalGraph f o -> RightnessGraph
rightnessGraph ng = _
  where
  rgDiamond =
    List.foldl' (\rg0 w ->
      List.foldl' (\rg1 e_l ->
        Map.alter (\case
          Just succs ->
            Just (List.foldl' (flip Set.insert) succs (rightPath w))
          Nothing ->
            Just (Set.fromList (rightPath w)))
          e_l rg1)
        rg0
        (leftPath w))
      Map.empty
      wedges

  wedges = carets ng ++ vees ng

-- A bit inefficient to do this in a different stage from detecting carets
-- and vees, but it's asymptotically the same and makes things a lot
-- simpler.
-- Returns
-- (edges belonging to a top tendril, edges belonging to a bottom tendril)
tendrils :: NaturalGraph f o -> (Set Edge, Set Edge)
tendrils ng = _
  where
  botTendrilous :: Vertex -> State (Set Edge) Bool
  botTendrilous v0 = loop (predsOf v0)
    where
    loop [] =
      return True -- if we got through everything, this vertex is tendrilous

    loop 

    loop (v : vs) =
      case botTendrilous v of
        True ->
          modify (Set.insert (Edge {source=v,sink=v0,sourceIndex=findSourceIndex v}))

        False ->
          return False

    findSourceIndex v = case v of

  predsOf = _
  
  top =
    flip execState $
      forM_ 

  g = digraph ng

  -- Make tail recursive if need be
  predsReg :: Vertex -> Maybe (Set Edge)
  predsReg r =
    let VertexData {incoming} = lookupExn r g in
    fmap Set.unions (mapM predsReg _)


{-
  goUpFrom :: ExplicitVert -> Set Edge -> Maybe (Set Edge)
  goUpFrom ev !acc = do

    speculative <- get
 -} 

vees :: NaturalGraph f o -> [Wedge]
vees = _
  where
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


carets :: NaturalGraph f o -> [Wedge]
carets = _
