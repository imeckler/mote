module Mote.Search.PurePoset where

import qualified Data.Set as Set
import Mote.Search.Poset.ElementData

type alias PosetStore k v
  = Set.Set k (ElementData k v)

fromHashPosetStore
  ::
