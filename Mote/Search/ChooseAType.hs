{-# LANGUAGE LambdaCase, NamedFieldPuns, TupleSections #-}
module Mote.Search.ChooseAType where

import Prelude hiding (lookup)
import TypeRep
import qualified Type
import Data.Monoid
import qualified Cloned.Unify as Unify
import qualified UniqFM
import Control.Monad.Reader
import Control.Applicative hiding (empty)
import Data.Maybe (mapMaybe)
import qualified VarEnv
import qualified Data.List as List
import qualified Name
import qualified OccName
import qualified FastString

{-
data TyConLookupTrie val
  = AllDone val
  | ChooseAnArg (ChooseAType (TyConLookupTrie val))
-}

data ChooseTyConArgs {- and you'll maybe get a -} val
  = AllDone val
  | ChooseAnArg (ChooseAType (ChooseTyConArgs val))
  deriving (Show)

newtype ChooseAppTy val
  = ChooseAppTy (Maybe (ChooseAType (ChooseAType val)))
  deriving (Show)

instance Functor ChooseAppTy where
  fmap f (ChooseAppTy cat) = ChooseAppTy (fmap (fmap (fmap f)) cat)

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
  , unifyWithATyVar :: VarEnv.VarEnv (Type.TyVar, val)
  -- [Type -> Type.TvSubstEnv -> ChooseM (Maybe (Type.TvSubstEnv, val))] -- [(Type.TyVar, val)]
      -- Gonna turn this into [(TyVar, val)]
-- The Real type      :: Type.TvSubstEnv -> Type -> ChooseM [Maybe (Type.TvSubstEnv, val)] -- [(Type.TyVar, val)]
--      :: {- Subst so far -} Type.TvSubstEnv -> Type -> ChooseM (Maybe (Type.TvSubstEnv, val))  -- I strongly suspect this should return a list of vals...
  , it'sAnAppTy :: ChooseAppTy val
  }

instance Show val => Show (ChooseAType val) where
  show (ChooseAType {it'sATyConTy, unifyWithATyVar, it'sAnAppTy}) =
    "ChooseAType { it'sATyConTy = "
    ++ show (UniqFM.ufmToList it'sATyConTy) ++ ", unifyWithATyVar = "
    ++ show (map (\(_, (v, x)) -> (varToString v, x)) (UniqFM.ufmToList unifyWithATyVar)) ++ ", it'sAnAppTy = "
    ++ "..." ++ " }"
    where
    varToString = FastString.unpackFS . OccName.occNameFS . Name.getOccName

instance Functor ChooseAType where
  fmap f (ChooseAType {it'sATyConTy, unifyWithATyVar, it'sAnAppTy}) =
    ChooseAType
      (fmap (fmap f) it'sATyConTy)
      (fmap (fmap f) unifyWithATyVar)
      (fmap f it'sAnAppTy)

lookupAppTy' :: ChooseAppTy val -> Type -> Type -> Type.TvSubstEnv -> [(Type.TvSubstEnv, val)]
lookupAppTy' (ChooseAppTy cat0May) t1 t2 subst =
  case cat0May of
    Nothing ->
      []

    Just cat0 ->
      concatMap
        (\(subst', cat') -> lookup' cat' t2 subst')
        (lookup' cat0 t1 subst)

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f = fmap concat . mapM f

lookup :: Type -> ChooseAType val -> [(Type.TvSubstEnv, val)]
lookup t cat = lookup' cat t Type.emptyTvSubstEnv

lookup' :: ChooseAType val -> Type -> Type.TvSubstEnv -> [(Type.TvSubstEnv, val)]
lookup' (ChooseAType {it'sAnAppTy, it'sATyConTy, unifyWithATyVar}) ty substSoFar =
  case ty of
    TyConApp tc args ->
      let
        appTyCase =
          case splitLast args of
            Nothing ->
              []

            Just (args', arg) ->
              lookupAppTy' it'sAnAppTy (TyConApp tc args') arg substSoFar
      in
         tyVarCase
      ++ (maybe [] (\ctc -> lookupTyConArgs' ctc args substSoFar) (UniqFM.lookupUFM it'sATyConTy tc))
      ++ appTyCase
      {-
      fmap (:[]) (unifyWithATyVar ty substSoFar)
      <> (UniqFM.lookupUFM tc it'sATyConTy >>= \ctc -> lookupTyConArgs' ctc args substSoFar)
      <> appTyCase -}

    FunTy t1 t2 ->
      maybe []
        (\ctc -> lookupTyConArgs' ctc [t1,t2] substSoFar)
        (UniqFM.lookupUFM it'sATyConTy Type.funTyCon)

    AppTy t1 t2 ->
      tyVarCase ++ lookupAppTy' it'sAnAppTy t1 t2 substSoFar

    TyVarTy _ -> tyVarCase


    -- TODO: For now
    _ ->
      error "TODO"

  where
  tyVarCase =
    let
      bindFlags _ = Unify.BindMe
    in
    mapMaybe
      (\(v,x) ->
        fmap (\subst' -> (subst', x))
        . unifyResultToMaybe
        $ Unify.unUM (Unify.uVar substSoFar v ty) bindFlags)
      (VarEnv.varEnvElts unifyWithATyVar)

-- TODO: This is going to be insanely inefficient. Will have to optimize
-- later.

empty :: ChooseAType val
empty =
  ChooseAType
    UniqFM.emptyUFM
    VarEnv.emptyVarEnv
    (ChooseAppTy Nothing)

singleton :: Type -> val -> ChooseAType val
singleton t x =
  case t of
    TyConApp tc args ->
      ChooseAType
      { it'sATyConTy = UniqFM.listToUFM [(tc, singletonTyConArgs args x)]
      , unifyWithATyVar = VarEnv.emptyVarEnv
      , it'sAnAppTy = ChooseAppTy Nothing
      }

    TyVarTy v ->
      ChooseAType
      { it'sATyConTy = UniqFM.emptyUFM
      , unifyWithATyVar = VarEnv.mkVarEnv [(v, (v, x))]
        {-
          \subst ty ->
            fmap
              (fmap (,x) . unifyResultToMaybe . Unify.unUM (Unify.uVar subst v ty))
              ask -}
      , it'sAnAppTy = ChooseAppTy Nothing
      }

    AppTy t1 t2 ->
      ChooseAType
      { it'sATyConTy = UniqFM.emptyUFM
      , unifyWithATyVar = VarEnv.emptyVarEnv
      , it'sAnAppTy =
          ChooseAppTy (Just (singleton t1 (singleton t2 x)))
      }

    FunTy t1 t2 ->
      -- I'm lazy
      singleton (TyConApp Type.funTyCon [t1, t2]) x

    LitTy {} -> error "ChooseAType.singleton: LitTy not implemented"
    ForAllTy {} -> error "ChooseAType.singleton: ForAllTy not implemented"


type GivenBindingRules = (->) (Type.TyVar -> Unify.BindFlag)

singletonTyConArgs :: [Type] -> val -> ChooseTyConArgs val
singletonTyConArgs args x =
  case args of
    [] ->
      AllDone x

    (arg : args') ->
      ChooseAnArg
        (singleton arg
          (singletonTyConArgs args' x))

insertTyConArgs = insertTyConArgsWith (\_old new -> new)

insertTyConArgsWith
  :: (val -> val -> val) -> [Type] -> val -> ChooseTyConArgs val -> ChooseTyConArgs val
insertTyConArgsWith = \f args x ctc ->
  case ctc of
    -- Args should be empty in this case.
    AllDone x' ->
      AllDone (f x' x)

    ChooseAnArg cat ->
      let (arg:args') = args in
      ChooseAnArg
        (updateAt
          (maybe (singletonTyConArgs args' x) (insertTyConArgsWith f args' x))
          arg
          cat)
       -- modifyAt (insertTyConArgsWith f args' x) arg cat)

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

updateAtAppTy :: (Maybe val -> val) -> Type -> Type -> ChooseAppTy val -> ChooseAppTy val
updateAtAppTy f t1 t2 (ChooseAppTy captMay) =
  case captMay of
    Nothing ->
      ChooseAppTy (Just (singleton t1 (singleton t2 (f Nothing))))
    Just capt ->
      ChooseAppTy (Just (updateAt (maybe (singleton t2 (f Nothing)) (updateAt f t2)) t1 capt))

  {-
    (updateAt (maybe (singleton t2 (f Nothing)) (updateAt f t2))
      t1 capt) -}

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
                (singletonTyConArgs args (f Nothing))
              -- UniqFM.addToUFM (it'sATyConTy cat) tc (f Nothing)
            Just ctc ->
              UniqFM.addToUFM (it'sATyConTy cat) tc
                (updateAtArgs f args ctc)
      }

    AppTy t1 t2 ->
      let
        ChooseAppTy captMay = it'sAnAppTy cat
        capt' =
          case captMay of
            Nothing ->
              singleton t1 (singleton t2 (f Nothing))
            Just capt ->
              updateAt (maybe (singleton t2 (f Nothing)) (updateAt f t2)) t1 capt
      in
      cat
      { it'sAnAppTy = ChooseAppTy (Just capt')
      }

    FunTy t1 t2 ->
      updateAt f (TyConApp Type.funTyCon [t1, t2]) cat

    TyVarTy v ->
      cat
      { unifyWithATyVar =
          case VarEnv.lookupVarEnv (unifyWithATyVar cat) v of
            Nothing ->
              VarEnv.extendVarEnv (unifyWithATyVar cat) v (v, f Nothing)

            Just (_, x) ->
              VarEnv.extendVarEnv (unifyWithATyVar cat) v (v, f (Just x))
      }

    LitTy {} ->
      error "updateAt: LitTy not implemented"

    ForAllTy {} ->
      error "updateAt: ForAllTy not implemented"

fromList :: [(Type, val)] -> ChooseAType val
fromList = List.foldl' (\cat (t, v) -> insert t v cat) empty 

fromListWith :: (val -> val -> val) -> [(Type, val)] -> ChooseAType val
fromListWith f = List.foldl' (\cat (t, v) -> insertWith f t v cat) empty

insert :: Type -> val -> ChooseAType val -> ChooseAType val
insert = insertWith (\_old new -> new)

insertWith :: (val -> val -> val) -> Type -> val -> ChooseAType val -> ChooseAType val
insertWith f ty x cat =
  case ty of
    TyConApp tc args ->
      cat
      { it'sATyConTy =
          UniqFM.alterUFM
            (\case
              Just ctc ->
                Just (insertTyConArgsWith f args x ctc)

              Nothing ->
                Just (singletonTyConArgs args x))
            (it'sATyConTy cat)
            tc
      }

    AppTy t1 t2 ->
      let
        ChooseAppTy captMay = it'sAnAppTy cat
        capt' =
          case captMay of
            Nothing ->
              singleton t1 (singleton t2 x)
            Just capt ->
              insertWith (\old _ -> insertWith f t2 x old) t1 (singleton t2 x) capt
      in
      cat
      { it'sAnAppTy = ChooseAppTy (Just capt')
      }

    TyVarTy v ->
      cat
      { unifyWithATyVar =
          VarEnv.alterVarEnv
            (maybe (Just (v, x)) (\(_, x_old) -> Just (v, f x_old x)))
            (unifyWithATyVar cat)
            v
      }

    FunTy t1 t2 ->
      insertWith f (TyConApp Type.funTyCon [t1, t2]) x cat

    ForAllTy {} ->
      error "insertWith: ForAllTy not implemented"

    LitTy {} ->
      error "insertWith: LitTy not implemented"

lookupTyConArgs' :: ChooseTyConArgs val -> [Type] -> Type.TvSubstEnv -> [(Type.TvSubstEnv, val)]
lookupTyConArgs' ctc args subst =
  case ctc of
    AllDone x ->
      [(subst, x)]

    ChooseAnArg cat ->
      case args of
        (arg:args') ->
          concatMap
            (\(subst', cat') -> lookupTyConArgs' cat' args' subst')
            (lookup' cat arg subst)
        _ ->
          [] -- TODO: This is actually an error case, but it's happening somehow. Figure out why.

allData :: ChooseAType val -> [val]
allData (ChooseAType {it'sATyConTy, unifyWithATyVar, it'sAnAppTy = ChooseAppTy capt }) =
  map snd (VarEnv.varEnvElts unifyWithATyVar)
  ++ concatMap allDataArgs (UniqFM.eltsUFM it'sATyConTy)

allDataArgs :: ChooseTyConArgs val -> [val]
allDataArgs ctc = case ctc of
  AllDone x -> [x]
  ChooseAnArg carg -> concatMap allDataArgs (allData carg)

unifyResultToMaybe :: Unify.UnifyResultM x -> Maybe x
unifyResultToMaybe ux =
  case ux of
    Unify.Unifiable x -> Just x
    Unify.MaybeApart x -> Just x
    Unify.SurelyApart -> Nothing

-- TODO: This is only here to break a dependency cycle on Mote.Util. Modules should be
-- refactored.
splitLast :: [a] -> Maybe ([a], a)
splitLast [] = Nothing
splitLast xs = Just (splitLast' xs)
  where
  splitLast' :: [a] -> ([a], a)
  splitLast' [x]    = ([], x)
  splitLast' (x:xs) = let (xs', xf) = (splitLast' xs) in (x:xs', xf)
  splitLast' _      = error "Mote.Search.splitLast': Impossible"

