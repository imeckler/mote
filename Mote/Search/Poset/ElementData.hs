{-# LANGUAGE RecordWildCards #-}
module Mote.Search.Poset.ElementData where

import qualified Data.Set as Set
import qualified Data.Map as Map
import Outputable (Outputable, ppr, ptext, (<+>), braces, fsep, punctuate, comma)
import FastString (sLit)
import Data.Monoid ((<>))

data ElementData k v =
  ElementData
  { above :: Set.Set k
  , below :: Set.Set k
  , value :: v
  }
  deriving (Show, Eq)

instance (Monoid v, Ord k) => Monoid (ElementData k v) where
  mempty = ElementData mempty mempty mempty
  mappend (ElementData abv1 bel1 v1) (ElementData abv2 bel2 v2) =
    ElementData (abv1 <> abv2) (bel1 <> bel2) (v1 <> v2)

instance (Outputable k, Outputable v) => Outputable (ElementData k v) where
  ppr (ElementData {..}) =
    ptext (sLit "ElementData") <+>
      braces
        (fsep
          (punctuate comma 
            [ ptext (sLit "above =") <+> ppr above
            , ptext (sLit "below =") <+> ppr below
            , ptext (sLit "value =") <+> ppr value
            ]))

