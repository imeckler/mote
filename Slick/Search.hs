{-# LANGUAGE TupleSections, RecordWildCards, LambdaCase, NamedFieldPuns #-}

module Slick.Search where

import Slick.Types
import Slick.Util
import Search.Graph
import Search.Types
import Slick.Suggest
import Slick.Holes
import Control.Arrow (first)

import TysPrim (funTyCon)
import TypeRep
import Type (splitForAllTys)
import TyCon
import Var

-- search :: M [NaturalGraph f]
search stRef = do
  FileData {typecheckedModule} <- getFileDataErr stRef
  ahi@(AugmentedHoleInfo {holeInfo}) <- getCurrentHoleErr stRef 
  suggs <- getAndMemoizeSuggestions stRef ahi
  (sug, startTy) <- headErr suggs
  let goalTy = holeType holeInfo
  return $ go _ startTy goalTy
  where
  go transes startTy goalTy  =
    let (startFs, _) = extractFunctors startTy
        (goalFs, _)  = extractFunctors goalTy
    in
    programsOfLengthAtMost transes 6 startFs goalFs

-- Write a type t as (A1 * ... * An)F where
-- each Ai and F are functors over a variable x
normalForm :: Var -> Type -> Maybe ([Func], Func)
normalForm x t = case t of
  TyVarTy v        ->
    if v == x then ([], SyntacticFuncs []) else ([], ConstFunc (WrappedType t))
  TyConApp tc kots -> _
  FunTy t t'       ->
    let (
        (fs, f) = normalForm x t'

  LitTy tl         -> ([], ConstFunc (WrappedType t))
  ForAllTy v t     -> Nothing -- TODO
  AppTy t t'       -> Nothing -- TODO

-- Checks if the type can be thought of as being of the form
-- forall a. F a -> G a
-- perhaps after partially applying.
-- (Of course F and G could be constant functors...but we don't
-- consider that case now. Maybe later, I guess there's no reason
-- not to.)
-- So, we are looking for types of the form
-- forall a. _ -> ... -> _ -> F a -> _ -> ... -> G a
-- It's really not unique since we can view 
-- forall a. F1 a -> F2 a -> G a as
-- F1 -> G
-- F2 -> G
-- (F1 * F2) -> G
--
-- either :: (a -> c) -> (b -> c) -> Either a b -> c
--  (^a * ^b) -> 1        (partially apply the Either argument)
--  (^a * ^b) -> ^(a + b) (don't partially apply the either argument
--

-- For simplicity, let's only do things which are really syntactically
-- of the form forall a. F a -> G a for now.
-- In fact, even this is wrong since extractFunctors pulls out the
asTrans :: Type -> Maybe (Trans SyntacticFunc)
asTrans t = case splitForAllTys t of
  (vs@(_:_), FunTy t1 t2) ->
    let (fs1, inner1) = extractFunctors t1
        (fs2, inner2) = extractFunctors t2
    in
    _
  _                       -> Nothing

type SyntacticFunc = (TyCon, [WrappedType])
data Func
  = SyntacticFunc SyntacticFunc
  | ConstFunc WrappedType
  deriving (Eq)

extractFunctors :: Type -> ([SyntacticFunc], WrappedType)
extractFunctors t = case t of
  TyVarTy v        -> ([], WrappedType t)
  TyConApp tc kots -> case splitLast kots of
    Nothing          -> ([], WrappedType t)
    Just (args, arg) -> first ((tc, map WrappedType args) :)
                        $ extractFunctors arg
  FunTy t t'       -> first ((funTyCon,[WrappedType t]) :) $ extractFunctors t'
  ForAllTy v t     -> extractFunctors t
  LitTy tl         -> ([], WrappedType t)
  AppTy t t'       -> error "extractFunctors: TODO AppTy" -- TODO
  where
  splitLast' :: [a] -> ([a], a)
  splitLast' [x]    = ([], x)
  splitLast' (x:xs) = first (x:) (splitLast' xs)

  splitLast :: [a] -> Maybe ([a], a)
  splitLast [] = Nothing
  splitLast xs = Just (splitLast' xs)

newtype WrappedType = WrappedType Type
instance Eq WrappedType where
  (==) (WrappedType t) (WrappedType t') = eqTy t t'

instance Ord WrappedType where
  compare (WrappedType t) (WrappedType t') = compareTy t t'

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

  o -> o
  where
  conOrd :: Type -> Int
  conOrd x = case x of
    TyVarTy v        -> 0
    AppTy t t'       -> 1
    TyConApp tc kots -> 2
    FunTy t t'       -> 3
    ForAllTy v t     -> 4
    LitTy tl         -> 5

  lex :: [Ordering] -> Ordering
  lex = (\case { [] -> EQ; (o:_) -> o } ) . dropWhile (== EQ)
{-
TyConApp IO
  [TyConApp Free
    [ TyConApp "[]" []
    , TyConApp Maybe [TyConApp Int]
    ]
  ]
-}
