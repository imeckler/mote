{-# LANGUAGE LambdaCase, NamedFieldPuns, TupleSections #-}
module LookupTrie where

import Prelude hiding (lookup)
import qualified Data.Map as Map
import TyCon
import TypeRep
import qualified Type
import Data.Monoid
import Mote.Util
import Mote.Search.WrappedType
import qualified Cloned.Unify as Unify
import qualified UniqFM
import Control.Monad.Reader
import Control.Applicative hiding (empty)
import Data.Maybe (maybeToList)

{-
data TyConLookupTrie val
  = AllDone val
  | ChooseAnArg (ChooseAType (TyConLookupTrie val))
-}

type ChooseM = Reader (Type.TyVar -> Unify.BindFlag)

data ChooseTyConArgs {- and you'll maybe get a -} val
  = AllDone val
  | ChooseAnArg (ChooseAType (ChooseTyConArgs val))

newtype ChooseAppTy val
  = ChooseAppTy (ChooseAType (ChooseAType val))

instance Functor ChooseAppTy where
  fmap f (ChooseAppTy cat) = ChooseAppTy (fmap (fmap f) cat)

instance Functor ChooseTyConArgs where
  fmap f ctc =
    case ctc of
      AllDone x ->
        f x
      ChooseAnArg ctc' ->
        ChooseAnArg (fmap (fmap f) ctc')

data ChooseAType {- and you'll maybe get a -} val
  = ChooseAType
  { it'sATyConTy    :: UniqFM.UniqFM (ChooseTyConArgs val) -- Think of it as `TyCon -> Maybe (ChooseTyConArgs val)`
  , unifyWithATyVar
      -- Gonna turn this into [(TyVar, val)]
      :: {- Subst so far -} Type.TvSubstEnv -> Type -> ChooseM (Maybe (Type.TvSubstEnv, val))  -- I strongly suspect this should return a list of vals...
  , it'sAnAppTy :: ChooseAppTy val
  }

instance Functor ChooseAType where
  fmap f (ChooseAType {it'sATyConTy, unifyWithATyVar, it'sAnAppTy}) =
    ChooseAType
      (fmap f it'sATyConTy)
      (\subst ty -> fmap (fmap (fmap f)) (unifyWithATyVar subst ty))
      (fmap f it'sAnAppTy)

lookupAppTy' :: ChooseAppTy val -> Type -> Type -> Type.TvSubstEnv -> ChooseM [(Type.TvSubstEnv, val)]
lookupAppTy' (ChooseAppTy cat0) t1 t2 subst =
  lookup' cat0 t1 subst >>= concatMapM (\(subst', cat') -> lookup' cat' t2 subst')
  where
  concatMapM f = fmap concat . mapM f

lookup' :: ChooseAType val -> Type -> Type.TvSubstEnv -> ChooseM [(Type.TvSubstEnv, val)]
lookup' (ChooseAType {it'sAnAppTy, it'sATyConTy, unifyWithATyVar}) ty substSoFar =
  case ty of
    TyConApp tc args ->
      let
        appTyCase =
          case splitLast args of
            Nothing ->
              return []

            Just (args', arg) ->
              lookupAppTy' it'sAnAppTy (TyConApp tc args') arg substSoFar
      in
      (\c1 c2 c3 -> c1 <> c2 <> c3)
      <$> (fmap (:[]) (unifyWithATyVar ty substSoFar))
      <*> (maybe (return []) (\ctc -> lookupTyConArgs' ctc args substSoFar) (UniqFM.lookupUFM it'sATyConTy tc))
      <*> appTyCase
      {-
      fmap (:[]) (unifyWithATyVar ty substSoFar)
      <> (UniqFM.lookupUFM tc it'sATyConTy >>= \ctc -> lookupTyConArgs' ctc args substSoFar)
      <> appTyCase -}

    FunTy t1 t2 ->
      maybe (return []) (\ctc -> lookupTyConArgs' ctc [t1,t2] substSoFar)
        (UniqFM.lookupUFM it'sATyConTy Type.funTyCon)

    AppTy t1 t2 ->
      liftA2 (<>)
        (fmap (:[]) (unifyWithATyVar ty substSoFar))
        (lookupAppTy' it'sAnAppTy t1 t2 substSoFar)

    TyVarTy _ ->
      fmap (maybeToList) (unifyWithATyVar substSoFar ty)

    -- TODO: For now
    _ ->
      _

-- TODO: This is going to be insanely inefficient. Will have to optimize
-- later.

empty :: ChooseAType val
empty =
  ChooseAType mempty (\_ _ -> Nothing) (ChooseAppTy mempty) -- Polymorphic recursion on values...

singleton :: Type -> val -> ChooseAType val
singleton t x =
  case t of
    TyConApp tc args ->
      ChooseAType
      { it'sATyConTy = Map.singleton tc (singletonTyConArgs args x) 
      , unifyWithATyVar = \_ _ -> Nothing
      , it'sAnAppTy = ChooseAppTy empty
      }

    TyVarTy v ->
      ChooseAType
      { it'sATyConTy = mempty
      , unifyWithATyVar =
          \subst ty ->
            fmap
              (fmap (,x) . unifyResultToMaybe . Unify.unUM (Unify.uVar subst v ty))
              ask
      , it'sAnAppTy = ChooseAppTy empty
      }

    AppTy t1 t2 ->
      ChooseAType
      { it'sATyConTy = mempty
      , unifyWithATyVar = \_ _ -> return Nothing
      }

singletonTyConArgs :: [Type] -> val -> ChooseTyConArgs val
singletonTyConArgs args x =
  case args of
    [] ->
      AllDone x

    (arg : args') ->
      ChooseAnArg (singleton arg (singletonTyConArgs args' x))

insertTyConArgs = insertTyConArgsWith (\old new -> new)

insertTyConArgsWith :: (val -> val -> val) -> [Type] -> val -> ChooseTyConArgs val -> ChooseTyConArgs val
insertTyConArgsWith = \f args x ctc ->
  case ctc of
    -- Args should be empty in this case.
    AllDone x' ->
      AllDone f x' x

    ChooseAnArg cat ->
      let (arg:args') = args in
      ChooseAnArg
        (updateAt
          (maybe (singletonTyConArgs args' x) (insertTyConArgsWith f args x))
          arg
          cat)
       -- modifyAt (insertTyConArgsWith f args' x) arg cat)
  where
  updateAtArgs :: (Maybe val -> val) -> [Type] -> ChooseTyConArgs val -> ChooseTyConArgs val
  updateAtArgs f args ctc =
    case ctc of
      AllDone x ->
        AllDone (f (Just x))

      ChooseAnArg cat ->
        let (arg:args') = args in
        ChooseAnArg
          (updateAt
            (maybe (singletonTyConArgs args' (f Nothing)) (updateAtArgs f args'))
            arg
            cat)

  updateAt :: (Maybe val -> val) -> Type -> ChooseAType val -> ChooseAType val
  updateAt f ty cat =
    case ty of
      TyConApp tc args ->
        cat
        { it'sATyConTy =
            case UniqFM.lookupUFM (it'sATyConTy cat) tc of
              Nothing ->
                UniqFM.addToUFM (it'sATyConTy cat) tc (f Nothing)
              Just ctc ->
                UniqFM.addToUFM (it'sATyConTy cat) tc
                  (updateAtArgs f args ctc)
        }

insertWith :: (val -> val -> val) -> Type -> val -> ChooseAType val -> ChooseAType val
insertWith f ty x cat =
  case ty of
    TyConApp tc args ->
      cat
      { it'sATyConTy =
          Map.alter
            (\case
              Just ctc -> Just (insertTyConArgs args x ctc)
              Nothing -> Just (singletonTyConArgs x args))
            tc
            (it'sATyConTy cat)
      }

lookupTyConArgs' :: ChooseTyConArgs val -> [Type] -> Type.TvSubstEnv -> ChooseM [(Type.TvSubstEnv, val)]
lookupTyConArgs' = _

unifyResultToMaybe :: Unify.UnifyResultM x -> Maybe x
unifyResultToMaybe ux =
  case ux of
    Unify.Unifiable x -> Just x
    Unify.MaybeApart x -> Just x
    Unify.SurelyApart -> Nothing
