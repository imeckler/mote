module Mote.Search.TypePoset where

import Mote.Search.WrappedType
import Mote.Search.NatTransData
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map as Map
import Type

data ArgsGroupingTree x
  = ArgsGroupingTree
  { chooseArg :: Map.Map WrappedType (Either (ArgsGroupingTree x) x)
  , argsNotThuslyGrouped :: Map.Map [WrappedType] x
  }

type TypePoset
  = Map.Map WrappedType
      ( ElementData WrappedType (NatTransData () Type)
      , Maybe
        (ArgsGroupingTree
          (HashMap.HashMap
            (Int, Int)
            (NatTransData () Type)))
      )
