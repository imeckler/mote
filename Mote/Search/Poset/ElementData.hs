{-# LANGUAGE RecordWildCards #-}
module Mote.Search.Poset.ElementData where

import qualified Data.Set as Set
import Outputable (Outputable, ppr, ptext, (<+>), braces, fsep, punctuate, comma)
import FastString (sLit)

data ElementData k v =
  ElementData
  { above :: Set.Set k
  , below :: Set.Set k
  , value :: v
  }
  deriving (Show, Eq)

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

