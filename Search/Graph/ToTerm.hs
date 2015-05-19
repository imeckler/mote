module Search.Graph.ToTerm where

import Search.Graph.Types
import Search.Graph.Types.Vertex

import qualified Data.Map as M
import Data.Map (Map)

data FreeNaturalGraph f = NaturalGraph
  { incomingLabels :: [f]
  , incomingSuccs  :: Map DummyVertex Vert
  , incomingCount  :: Int

  , outgoingPreds  :: Map DummyVertex Vert
  , outgoingCount  :: Int

  , digraph        :: Map Vertex (VertexData f)
  }
  deriving (Show)

