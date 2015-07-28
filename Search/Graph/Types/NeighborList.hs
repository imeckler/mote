{-# LANGUAGE LambdaCase #-}
module Search.Graph.Types.NeighborList where

import Prelude hiding (Word)
import Data.Monoid
import Data.Bifunctor
import Search.Graph.Types.Vertex
import Search.Types.Word (Word(..))
import qualified Search.Types.Word as Word

-- If an edge is foggy then every edge to its right should be as well
data NeighborList f o
  = WithFogged [(OrBoundary Vertex, f)] (Word f o) -- technically this Word f o should be nonempty
  | NoFogged (Word (OrBoundary Vertex, f) (OrBoundary Vertex, o))
  deriving (Show, Eq, Ord)

length :: NeighborList f o -> Int
length = \case
  NoFogged w -> Word.length w
  WithFogged pre w -> Prelude.length pre + Word.length w

juxtapose :: NeighborList f o -> NeighborList f o -> NeighborList f o
juxtapose nl1 nl2 =
  case (nl1, nl2) of
    (NoFogged w, NoFogged w') ->
      NoFogged (w <> w') -- dangerous..

    (NoFogged w, WithFogged unfogged w') ->
      case w of
        Word fs (Just o) -> nl1 -- dangerous..
        Word fs Nothing -> WithFogged (fs ++ unfogged) w'

    (WithFogged unfogged w, NoFogged w') ->
      WithFogged unfogged (w <> bimap snd snd w')

    (WithFogged unfogged w, WithFogged unfogged' w') ->
      WithFogged unfogged (w <> Word (map snd unfogged') Nothing <> w')

instance Monoid (NeighborList f o) where
  mempty = NoFogged mempty
  mappend = juxtapose

-- Mote was awesome for this instance
instance Bifunctor NeighborList where
  first g = \case
    NoFogged w -> NoFogged (first (second g) w)
    WithFogged pre w -> WithFogged (map (second g) pre) (first g w)

  second g = \case
    NoFogged w -> NoFogged (second (second g) w)
    WithFogged pre w -> WithFogged pre (second g w)

  bimap g1 g2 = \case
    NoFogged w -> NoFogged (bimap (second g1) (second g2) w)
    WithFogged pre w -> WithFogged (map (second g1) pre) (bimap g1 g2 w)

mapVertex :: (OrBoundary Vertex -> OrBoundary Vertex) -> NeighborList f o -> NeighborList f o
mapVertex f nl =
  case nl of
    WithFogged pre w -> WithFogged (map (first f) pre) w
    NoFogged w -> NoFogged (bimap (first f) (first f) w)

{-
fold :: (f -> s -> s) -> (o -> s -> s) -> s -> NeighborList f o -> s
fold f g z = \case
  NoFogged w -> Word.fold (f . snd) (g . _) z w
  WithFogged v_and_xs w -> _
-}

toList :: NeighborList (edgeID, f) (edgeID, o) -> [(Foggy (OrBoundary Vertex), edgeID)]
toList nl =
  case nl of
    WithFogged pre w ->
      map (\(bv, (e,_)) -> (Clear bv, e)) pre
      ++ Word.toList (bimap (\(e,_) -> (CoveredInFog, e)) (\(e,_) -> (CoveredInFog, e)) w)

    NoFogged w -> 
      let f (bv, (e,_)) = (Clear bv, e) in
      Word.toList (bimap f f w)
