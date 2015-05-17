{-# LANGUAGE BangPatterns, LambdaCase, NamedFieldPuns #-}
module Search.Graph.Types 
  ( VertexData (..)
  , NaturalGraph (..)
  , EdgeID
  , EdgeData (..)
  , module Search.Graph.Types.Vertex
  ) where

import Search.Types
import Data.Hashable
import qualified Data.Map as Map
import Data.Map (Map)
import qualified Data.Set as Set
import Data.Set (Set)
import Control.Monad.State
import qualified Search.Types.Word as Word
import Search.Graph.Types.NeighborList (NeighborList(..))
import Search.Graph.Types.Vertex
import qualified Data.List as List
import Data.Bifunctor

data VertexData f o = VertexData
  { label    :: TransName
  -- We store both the incoming and the outgoing vertices (in the proper
  -- order!) at every vertex to make traversal and obtaining the bimodal
  -- ordering easier. 
  , incoming :: NeighborList f o
  , outgoing :: NeighborList f o
  }
  deriving (Show, Eq)

instance Bifunctor VertexData where
 first f vd = vd { incoming = first f (incoming vd), outgoing = second f (outgoing vd) }

 second f vd = vd { incoming = second f (incoming vd), outgoing = second f (outgoing vd) }

 bimap f g vd = vd { incoming = bimap f g (incoming vd), outgoing = bimap f g (outgoing vd) }

type EdgeID = Int

data EdgeData = EdgeData 
  { source :: Foggy (OrBoundary Vertex)
  , sink   :: Foggy (OrBoundary Vertex)
  }

data NaturalGraph f o = NaturalGraph
  { top           :: NeighborList (EdgeID, f) (EdgeID, o)
  , bottom        :: NeighborList (EdgeID, f) (EdgeID, o)
  , digraph       :: Map Vertex (VertexData (EdgeID, f) (EdgeID, o))
  , edges         :: Map EdgeID EdgeData
  , constantEdges :: Set EdgeID -- For easy canonicalization
  }

-- It is convenient for edges to have ids. 

instance (Hashable f, Hashable o) => Eq (NaturalGraph f o) where
  (==) g1 g2 = hashWithSalt 0 g1 == hashWithSalt 0 g2 && hashWithSalt 10 g1 == hashWithSalt 10 g2

instance (Hashable f, Hashable o) => Hashable (NaturalGraph f o) where
  hashWithSalt = hashWithSaltGraph

hashWithSaltGraph :: (Hashable f, Hashable o) => Int -> NaturalGraph f o -> Int
hashWithSaltGraph s_orig ng =
  let
    vs = fromNeighborList (top ng)
    (s', _, _) = execState go (s_orig, Set.fromList (map fst vs), vs)
  in
  s'
  where
--  go :: State (Int, Set (OrBoundary Vertex), [(OrBoundary Vertex, Either f o)]) ()
  go = do
    (s, pushed, next) <- get -- :: State (Int, Set (OrBoundary Vertex), [OrBoundary Vertex])(Int, Set (OrBoundary Vertex), [(OrBoundary Vertex, f)])
    case next of
      [] -> return ()

       -- boundary means bottom in this function
      (Boundary, lab) : next' ->
        let
          s' = s `hashWithSalt` lab

          toPush = filter (\(bv,_) -> bv `Set.member` pushed) (fromNeighborList (bottom ng))
        in
        put (s', List.foldl' (flip Set.insert) pushed (map fst toPush), toPush ++ next')

      (Inner v, lab) : next' ->
        let
          Just (VertexData { label, incoming, outgoing }) =
            Map.lookup v g

          s' =
            (s `hashWithSalt` lab) `hashWithSalt` label

          toPush =
            filter (\(bv, _) -> bv `Set.member` pushed) (fromNeighborList incoming ++ fromNeighborList outgoing)
        in
        put (s', List.foldl' (flip Set.insert) pushed (map fst toPush), toPush ++ next')

  fromNeighborList =
    \case
      WithFogged pre w ->
        map (\(bv, (_,f)) -> (bv, Left f)) pre

      NoFogged w ->
        Word.toList $
          bimap (\(bv,(_,f)) -> (bv, Left f)) (\(bv, (_,o)) -> (bv, Right o)) w

  g = digraph ng

