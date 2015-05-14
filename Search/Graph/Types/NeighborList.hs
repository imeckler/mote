{-# LANGUAGE LambdaCase #-}
module Search.Graph.Types.NeighborList where

import Data.Bifunctor
import Search.Graph.Types.Vertex
import Search.Types.Word (Word)
import qualified Search.Types.Word as Word

-- If an edge is foggy then every edge to its right should be as well
data NeighborList f o
  = WithFogged [(Vert, f)] (Word f o) -- technically this Word f o should be nonempty
  | NoFogged (Word (Vert, f) (Vert, o))
  deriving (Show, Eq, Ord)

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

{-
fold :: (f -> s -> s) -> (o -> s -> s) -> s -> NeighborList f o -> s
fold f g z = \case
  NoFogged w -> Word.fold (f . snd) (g . _) z w
  WithFogged v_and_xs w -> _
-}
