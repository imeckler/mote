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
import Data.Maybe (maybeToList, mapMaybe)

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
        AllDone (f x)

      ChooseAnArg ctc' ->
        ChooseAnArg (fmap (fmap f) ctc')

data ChooseAType {- and you'll maybe get a -} val
  = ChooseAType
  { it'sATyConTy    :: UniqFM.UniqFM (ChooseTyConArgs val) -- Think of it as `TyCon -> Maybe (ChooseTyConArgs val)`
  , unifyWithATyVar :: [Type -> Type.TvSubstEnv -> ChooseM (Maybe (Type.TvSubstEnv, val))] -- [(Type.TyVar, val)]
      -- Gonna turn this into [(TyVar, val)]
-- The Real type      :: Type.TvSubstEnv -> Type -> ChooseM [Maybe (Type.TvSubstEnv, val)] -- [(Type.TyVar, val)]
--      :: {- Subst so far -} Type.TvSubstEnv -> Type -> ChooseM (Maybe (Type.TvSubstEnv, val))  -- I strongly suspect this should return a list of vals...
  , it'sAnAppTy :: ChooseAppTy val
  , theBindingRules :: Type.TyVar -> Unify.BindFlag -- Should be unnecessary now.
  }

instance Functor ChooseAType where
  fmap f (ChooseAType {it'sATyConTy, unifyWithATyVar, it'sAnAppTy, theBindingRules}) =
    ChooseAType
      (fmap (fmap f) it'sATyConTy)
      (fmap (fmap f) unifyWithATyVar)
      (fmap f it'sAnAppTy)
      theBindingRules

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
      <$> tyVarCase
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
        tyVarCase
        (lookupAppTy' it'sAnAppTy t1 t2 substSoFar)

    TyVarTy _ -> tyVarCase


    -- TODO: For now
    _ ->
      error "TODO"

  where
  tyVarCase = do
    bindFlags <- ask
    return $
      mapMaybe
        (\(v,x) ->
          fmap (\subst' -> (subst', x))
          . unifyResultToMaybe
          $ Unify.unUM (Unify.uVar substSoFar v ty) bindFlags)
        unifyWithATyVar

-- TODO: This is going to be insanely inefficient. Will have to optimize
-- later.

empty :: GivenBindingRules (ChooseAType val)
empty rules =
  ChooseAType UniqFM.emptyUFM [] (ChooseAppTy (empty rules)) rules

singleton :: GivenBindingRules (Type -> val -> ChooseAType val)
singleton rules t x =
  case t of
    TyConApp tc args ->
      ChooseAType
      { it'sATyConTy = UniqFM.listToUFM [(tc, singletonTyConArgs rules args x)]
      , unifyWithATyVar = []
      , it'sAnAppTy = ChooseAppTy (empty rules)
      , theBindingRules = rules
      }

    TyVarTy v ->
      ChooseAType
      { it'sATyConTy = UniqFM.emptyUFM
      , unifyWithATyVar = [(v, x)]
        {-
          \subst ty ->
            fmap
              (fmap (,x) . unifyResultToMaybe . Unify.unUM (Unify.uVar subst v ty))
              ask -}
      , it'sAnAppTy = ChooseAppTy (empty rules)
      , theBindingRules = rules
      }

    AppTy t1 t2 ->
      ChooseAType
      { it'sATyConTy = UniqFM.emptyUFM
      , unifyWithATyVar = []
      , it'sAnAppTy =
          ChooseAppTy (singleton rules t1 (singleton rules t2 x))
      , theBindingRules = rules
      }

    FunTy t1 t2 ->
      -- I'm lazy
      singleton rules (TyConApp Type.funTyCon [t1, t2]) x

    LitTy {} -> error "ChooseAType.singleton: LitTy not implemented"
    ForAllTy {} -> error "ChooseAType.singleton: ForAllTy not implemented"


type GivenBindingRules = (->) (Type.TyVar -> Unify.BindFlag)

singletonTyConArgs :: GivenBindingRules ([Type] -> val -> ChooseTyConArgs val)
singletonTyConArgs rules args x =
  case args of
    [] ->
      AllDone x

    (arg : args') ->
      ChooseAnArg
        (singleton rules arg
          (singletonTyConArgs rules args' x))

insertTyConArgs rules = insertTyConArgsWith rules (\old new -> new)

insertTyConArgsWith
  :: GivenBindingRules 
    ((val -> val -> val) -> [Type] -> val -> ChooseTyConArgs val -> ChooseTyConArgs val)
insertTyConArgsWith rules = \f args x ctc ->
  case ctc of
    -- Args should be empty in this case.
    AllDone x' ->
      AllDone (f x' x)

    ChooseAnArg cat ->
      let (arg:args') = args in
      ChooseAnArg
        (updateAt
          (maybe (singletonTyConArgs rules args' x) (insertTyConArgsWith rules f args x))
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
            (maybe (singletonTyConArgs rules args' (f Nothing)) (updateAtArgs f args'))
            arg
            cat)

  updateAt :: (Maybe val -> val) -> Type -> ChooseAType val -> ChooseAType val
  updateAt f ty0 cat =
    case ty0 of
      TyConApp tc args ->
        cat
        { it'sATyConTy =
            case UniqFM.lookupUFM (it'sATyConTy cat) tc of
              Nothing ->
                UniqFM.addToUFM
                  (it'sATyConTy cat)
                  tc
                  (singletonTyConArgs (theBindingRules cat) args (f Nothing))
                -- UniqFM.addToUFM (it'sATyConTy cat) tc (f Nothing)
              Just ctc ->
                UniqFM.addToUFM (it'sATyConTy cat) tc
                  (updateAtArgs f args ctc)
        }

      TyVarTy v ->
        cat
        { unifyWithATyVar =
            map (\f ty subst -> fmap (fmap (fmap (f . Just))) $ f ty subst) (unifyWithATyVar cat)
          {-
            map
              (\(v, x) ->
                ( v
                , maybe _ _ (unifyResultToMaybe _)
                ))
              (unifyWithATyVar cat) -}
        }

insertWith :: (val -> val -> val) -> Type -> val -> ChooseAType val -> ChooseAType val
insertWith f ty x cat =
  case ty of
    TyConApp tc args ->
      cat
      { it'sATyConTy =
          UniqFM.alterUFM
            (\case
              Just ctc -> Just (insertTyConArgs (theBindingRules cat) args x ctc)
              Nothing -> Just (singletonTyConArgs (theBindingRules cat) args x))
            (it'sATyConTy cat)
            tc
      }

lookupTyConArgs' :: ChooseTyConArgs val -> [Type] -> Type.TvSubstEnv -> ChooseM [(Type.TvSubstEnv, val)]
lookupTyConArgs' = error "TODO"

unifyResultToMaybe :: Unify.UnifyResultM x -> Maybe x
unifyResultToMaybe ux =
  case ux of
    Unify.Unifiable x -> Just x
    Unify.MaybeApart x -> Just x
    Unify.SurelyApart -> Nothing
