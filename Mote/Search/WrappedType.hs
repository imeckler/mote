{-# LANGUAGE LambdaCase #-}
module Mote.Search.WrappedType where

import Outputable
import Data.Hashable
import TypeRep
import Unique
import qualified Data.List as List
import Type (cmpType)

newtype WrappedType = WrappedType { unwrapType :: Type }
instance Eq WrappedType where
  (==) (WrappedType t) (WrappedType t') = eqTy t t'

instance Ord WrappedType where
  compare (WrappedType t) (WrappedType t') = cmpType t t'

instance Outputable WrappedType where
  ppr (WrappedType t) = ppr t
  pprPrec r (WrappedType t) = pprPrec r t

-- Hacky syntactic equality for Type so that it can be used as the functor
-- parameter in all the Search types
eqTy :: Type -> Type -> Bool
eqTy x y = case (x, y) of
  (AppTy t1 t2, AppTy t1' t2')           -> eqTy t1 t1' && eqTy t2 t2'
  (TyConApp tc kots, TyConApp tc' kots') -> tc == tc' && and (zipWith eqTy kots kots')
  (FunTy t1 t2, FunTy t1' t2')           -> eqTy t1 t1' && eqTy t2 t2'
  (ForAllTy v t, ForAllTy v' t')         -> v == v' && eqTy t t'
  (LitTy tl, LitTy tl')                  -> tl == tl'
  (TyVarTy v, TyVarTy v')                -> v == v'
  _                                      -> False

instance Hashable WrappedType where
  hashWithSalt s (WrappedType t) = hashTypeWithSalt s t

hashTypeWithSalt :: Int -> Type -> Int
hashTypeWithSalt s t = case t of
  TyVarTy v        -> s `hashWithSalt` (0::Int) `hashWithSalt` getKey (getUnique v)
  AppTy t t'       -> s `hashWithSalt` ((1::Int) `hashTypeWithSalt` t) `hashTypeWithSalt` t'
  TyConApp tc kots -> List.foldl' hashTypeWithSalt (s `hashWithSalt` (2::Int) `hashWithSalt` getKey (getUnique tc)) kots
  FunTy t t'       -> s `hashWithSalt` (3::Int) `hashTypeWithSalt` t `hashTypeWithSalt` t'
  ForAllTy v t     -> s `hashWithSalt` ((4::Int) `hashWithSalt` getKey (getUnique v)) `hashTypeWithSalt` t
  LitTy tl         -> s `hashWithSalt` (5::Int) `hashTyLitWithSalt` tl

hashTyLitWithSalt s tl = case tl of
  NumTyLit n  -> s `hashWithSalt` n
  StrTyLit fs -> s `hashWithSalt` getKey (getUnique fs)

{-
compareTy :: Type -> Type -> Ordering
compareTy = \x y -> case compare (conOrd x) (conOrd y) of
  EQ ->
    case (x, y) of
      (AppTy t1 t2, AppTy t1' t2') ->
        lex [compareTy t1 t1', compareTy t2 t2']

      (TyConApp tc kots, TyConApp tc' kots') ->
        lex (compare tc tc' : zipWith compareTy kots kots')

      (FunTy t1 t2, FunTy t1' t2') ->
        lex [compareTy t1 t1', compareTy t2 t2']

      (ForAllTy v t, ForAllTy v' t') ->
        lex [compare v v', compareTy t t']

      (LitTy tl, LitTy tl') -> compare tl tl'

      (TyVarTy v, TyVarTy v') -> compare v v'

      _ -> error "Mote.Search.compareTy: Impossible"

  o -> o
  where
  conOrd :: Type -> Int
  conOrd x = case x of
    TyVarTy {}  -> 0
    AppTy {}    -> 1
    TyConApp {} -> 2
    FunTy {}    -> 3
    ForAllTy {} -> 4
    LitTy {}    -> 5

  lex :: [Ordering] -> Ordering
  lex = (\case { [] -> EQ; (o:_) -> o } ) . dropWhile (== EQ)
               -}
