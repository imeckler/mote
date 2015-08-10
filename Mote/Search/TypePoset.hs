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

instance Monoid x => Monoid (ArgsGroupingTree x) where
  mempty = ArgsGroupingTree mempty mempty
  mappend (ArgsGroupingTree chooseArg1 ungrouped1) (ArgsGroupingTree chooseArg2 ungrouped2) =
    ArgsGroupingTree
      (Map.unionWith (\ex1 ex2 ->
        case (ex1, ex2) of
          (Left at1, Left at2) -> Left (at1 `mappend` at2)
          (Right x1, Right x2) -> Right (x1 `mappend` x2)
          _ -> ex1)
        chooseArg1 chooseArg2)
      (Map.unionWith mappend ungrouped1 ungrouped2)


type TypePoset
  = Map.Map WrappedType
      ( ElementData WrappedType (NatTransData () Type)
      , Maybe
        (ArgsGroupingTree
          (HashMap.HashMap
            (Int, Int)
            (NatTransData () Type)))
      )

data TypeLookupTable
  = TypeLookupTable
  { byClosedType :: Map.Map WrappedType (HashMap.HashMap (Int, Int) (NatTransData () Type))
  , lookupPoset :: TypePoset
  }


data ElementData key val
  = ElementData
  { moreGeneral   :: Map.Map key Type.TvSubst
  , lessGeneral   :: Map.Map key Type.TvSubst
  , natTranses    :: HashMap.HashMap (Int, Int) val -- (NatTransData () Type)
  }

type ElementData'
  = ElementData WrappedType (NatTransData () Type)

