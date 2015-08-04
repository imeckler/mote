module Mote.Search.Poset.Pure where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Mote.Search.Poset.ElementData
import qualified Data.HashTable.IO as HashTable
import Control.Monad.IO.Class (MonadIO(..))
import Data.Hashable (Hashable)

type PosetStore k v
  = Map.Map k (ElementData k v)

fromHashPosetStore
  :: (MonadIO m, Hashable k, Ord k, Monoid v)
  => HashTable.BasicHashTable k (ElementData k v) 
  -> m (PosetStore k v)
fromHashPosetStore hashPoset =
  fmap (Map.fromListWith mappend)
    (liftIO (HashTable.toList hashPoset))

