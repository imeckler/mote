{-# LANGUAGE DeriveFunctor #-}
module Search.Graph.Types.Vertex where

type Vertex      = Int
type DummyVertex = Vertex

-- In our context, we work with digraphs where some subsets of the edges
-- are detached at one of their terminals. Specifically, there is a set
-- of "incoming" edges which have no source, and "outgoing" edges which
-- have no target. Furthermore both these sets are ordered "left to right"
data Vert 
  = Real Vertex
  | Dummy DummyVertex
  deriving (Show, Eq, Ord)

data Foggy a
  = Clear a
  | CoveredInFog
  deriving (Show, Eq, Ord, Functor)

data InOrOut = In | Out
  deriving (Show, Eq, Ord)

data OrBoundary a = Boundary | Inner a
  deriving (Show, Eq, Ord, Functor)

-- We occasionally require this representation. Notably in
-- connectedComponents (and we could have used it in
-- isomorphic/hashWithSaltGraph).
data UnambiguousVert
  = UReal Vertex
  | UDummy InOrOut Int -- TODO: this Int should be EdgeID
  deriving (Show, Eq, Ord)

