{-# LANGUAGE LambdaCase, NamedFieldPuns, RecordWildCards #-}
module Mote.Search.NatTransData where

import qualified Search.Types.Word as Word
import Mote.Search.WrappedType
import Data.Hashable
import Outputable (Outputable(..), (<+>), ptext, braces, fsep, punctuate, comma)
import Data.Monoid
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import           FastString              (sLit)
import TyCon
import Var
import Unique
import qualified Data.Map as Map
import qualified Data.HashMap.Strict as HashMap
import Control.Applicative
import Type
import Name

data TypeFunction
  = TypeFunctionTyCon TyCon
  | TypeFunctionTyVar Var
  deriving (Eq, Ord)

instance Hashable TypeFunction where
  hashWithSalt s cf =
    case cf of
      TypeFunctionTyVar v ->
        s `hashWithSalt` (0::Int) `hashWithSalt` getKey (getUnique v)

      TypeFunctionTyCon tc ->
        s `hashWithSalt` (1::Int) `hashWithSalt` getKey (getUnique tc)

instance Outputable TypeFunction where
  ppr = \case
    TypeFunctionTyCon tc ->
      ptext (sLit "TypeFunctionTyCon") <+> ppr tc

    TypeFunctionTyVar v ->
      ptext (sLit "TypeFunctionTyVar") <+> ppr v

data ConstantFunctor
  = ConstantFunctorTyVar Var
  | ConstantFunctorTyCon TyCon
  deriving (Eq)

instance Hashable ConstantFunctor where
  hashWithSalt s cf =
    case cf of
      ConstantFunctorTyVar v ->
        s `hashWithSalt` (0::Int) `hashWithSalt` getKey (getUnique v)

      ConstantFunctorTyCon tc ->
        s `hashWithSalt` (1::Int) `hashWithSalt` getKey (getUnique tc)

instance Outputable ConstantFunctor where
  ppr = \case
    ConstantFunctorTyCon tc ->
      ptext (sLit "ConstantFunctorTyCon") <+> ppr tc

    ConstantFunctorTyVar v ->
      ptext (sLit "ConstantFunctorTyVar") <+> ppr v

type SyntacticFunctor
  = ( TypeFunction, [ WrappedType ] )


data NatTransData context constant
  = NatTransData
  { name                    :: Name
  , context                 :: context
  , from                    :: Word.Word SyntacticFunctor constant
  , to                      :: Word.Word SyntacticFunctor constant
  , functorArgumentPosition :: Int
  , numberOfArguments       :: Int
  -- TODO: I essentially don't use the fact that from or to are Words
  -- anymore, so they should really both be chnaged to type when I get the
  -- chance. This "toType" field is a holdover til then. It might be
  -- slightly more efficient to do substition on words, but I doubt it will
  -- be mucb more
  , toType                  :: Type
  , fromType                :: Type
  }
  deriving (Eq)

instance (Hashable constant, Hashable context) => Hashable (NatTransData context constant) where
  hashWithSalt s (NatTransData {..}) =
    s `hashWithSalt`
    getKey (getUnique name) `hashWithSalt`
    context `hashWithSalt`
    from `hashWithSalt`
    to `hashWithSalt`
    functorArgumentPosition `hashWithSalt`
    numberOfArguments

instance (Outputable context, Outputable constant) => Outputable (NatTransData context constant) where
  ppr (NatTransData {..}) =
    ptext (sLit "NatTransData") <+>
      braces
        (fsep
          (punctuate comma 
            [ ptext (sLit "name =") <+> ppr name
            , ptext (sLit "context =") <+> ppr context
            , ptext (sLit "from =") <+> ppr from
            , ptext (sLit "to =") <+> ppr to
            , ptext (sLit "functorArgumentPosition =") <+> ppr functorArgumentPosition
            , ptext (sLit "numberOfArguments =") <+> ppr numberOfArguments
            ]))

instance Bifunctor NatTransData where
  first f nd = nd { context = f (context nd) }
  second f nd = nd { from = second f (from nd), to = second f (from nd) }

instance Bifoldable NatTransData where
  bifoldMap f g (NatTransData {context, from, to}) =
    f context <> foldMap g (Word.end from) <> foldMap g (Word.end to)

instance Bitraversable NatTransData where
  bitraverse f g nd =
    liftA3 (\context' from' to' -> nd { context = context', from = from', to = to' })
      (f (context nd))
      (bitraverse pure g (from nd)) -- TODO: Material: Holes were great here
      (bitraverse pure g (to nd))

