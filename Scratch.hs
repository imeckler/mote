{-# LANGUAGE LambdaCase, NamedFieldPuns, RecordWildCards, TupleSections, ViewPatterns #-}

module Scratch where

import           Prelude                 hiding (Word)
import           Control.Applicative
import           Control.Monad.Error
import           Data.Bifoldable
import           Data.Bifunctor
import           Data.Bitraversable
import           Data.Foldable
import Data.Function (on)
import           Data.Maybe              (catMaybes, isJust, isNothing, fromJust, mapMaybe, fromMaybe)
import           Data.Monoid
import Data.Hashable
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List

import           Mote.GhcUtil            (discardConstraints, addPredTys, splitPredTys)
import           Mote.Refine             (tcRnExprTc, subTypeEvTc)
import           Mote.Search.WrappedType
import           Mote.Types
import           Mote.Util
import           Search.Types.Word       (Word (..))
import qualified Search.Types.Word       as Word
-- import qualified Mote.Search.Poset as Poset
import Mote.Search.Poset
-- import qualified Mote.Search.Poset.ElementData as ElementData
import qualified Mote.Search.Poset.Pure as PurePoset
import qualified Mote.LoadFile as LoadFile

import qualified DynFlags
import HscTypes (hsc_dflags)
import           GHC
import OccName (mkVarOcc)
import Name (mkInternalName)
import qualified Name
import           RdrName                 (RdrName (Exact))
import           Type                    (splitAppTys, splitFunTys, mkForAllTys, TvSubst)
import qualified Type
import Kind (liftedTypeKind)
import           TypeRep                 (Type (..), tyVarsOfTypes, tyVarsOfType)
import Unique (getUnique, getKey)
import           UniqSet                 (elementOfUniqSet)
import qualified UniqSet
import           Var                     (Var, mkGlobalVar)
import qualified VarEnv
import TcRnMonad (newUnique, TcRnIf)
import IdInfo (IdDetails (VanillaId), vanillaIdInfo)
import qualified Bag
import qualified InstEnv
import qualified TcEnv
import qualified VarSet
import qualified UniqFM
import qualified Cloned.Unify
import qualified Unify
import qualified BasicTypes
import qualified Data.HashTable.IO as HashTable
import qualified TcType
import qualified Id
import qualified Data.HashMap.Strict as HashMap
import qualified PrelNames
import qualified Class
import qualified TyCon

import qualified Unsafe.Coerce

import           FastString              (sLit)
import           Outputable              (Outputable, comma, fsep, ppr, ptext,
                                          punctuate, showSDoc, (<+>), braces)
import qualified Outputable
import Cloned.Unify
import Debug.Trace

-- First we make a poset of the things in scope ordered by their
-- contextualized from types. This forms the skeleton of our DAG. We then
-- grow the DAG up from each node in the skeleton by generalizing
-- instances. We arrange things so that minimal elements of the DAG have
-- no demands placed on them.

-- Need to make sure that everyone gets the functions with the empty
-- context though.

type CanonicalContext = NatTransContext
type CanonicalFromType
  =
  ( CanonicalContext
  , Type
  )

canonicalize :: (NatTransContext, Type) -> CanonicalFromType
canonicalize (ctx, ty) =
  let
    ctx' = map (Type.getClassPredTys . unwrapType) ctx
  in
  _

-- This should usually be enough for cmpType to take us the rest of the
-- way.
-- partiallyCanonicalizeContext

type WrappedPredType
  = WrappedType

type NatTransContext
  = [WrappedPredType]

data TypeFunction
  = TypeFunctionTyCon TyCon
  | TypeFunctionTyVar Var
  deriving (Eq)

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

instance Hashable TypeFunction where
  hashWithSalt s cf =
    case cf of
      TypeFunctionTyVar v ->
        s `hashWithSalt` (0::Int) `hashWithSalt` getKey (getUnique v)

      TypeFunctionTyCon tc ->
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
  { name :: Name
  , context :: context
  , from :: Word SyntacticFunctor constant
  , to :: Word SyntacticFunctor constant
  , functorArgumentPosition :: Int
  , numberOfArguments :: Int
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
  bifoldMap f g (NatTransData {context, from, to}) = f context <> foldMap g (Word.end from) <> foldMap g (Word.end to)

instance Bitraversable NatTransData where
  bitraverse f g nd =
    liftA3 (\context' from' to' -> nd { context = context', from = from', to = to' })
      (f (context nd))
      (bitraverse pure g (from nd)) -- TODO: Material: Holes were great here
      (bitraverse pure g (to nd))

toStringyData :: GhcMonad m => NatTransData NatTransContext ConstantFunctor -> m (NatTransData [String] String)
toStringyData =
  bitraverse (traverse toStr) (\case
    ConstantFunctorTyCon tc -> toStr tc
    ConstantFunctorTyVar v -> toStr v)
  where
  toStr o = fmap (\fs -> showSDoc fs (ppr o)) getSessionDynFlags

isReasonableTrans :: NatTransData context constant -> Bool
isReasonableTrans nd = numberOfArguments nd < 4

-- TODO: Check that no other arg of targSfs contains the inner poly var
-- TODO: Should disallow transes whose from ConstantFunctor is a tyvar
-- different from the innerpolyvar of the target
natTransInterpretations :: (Name, Type) -> [NatTransData NatTransContext ConstantFunctor]
natTransInterpretations (name, t0) =
  filter isReasonableTrans $ catMaybes (zipWith interp [0..] args)
  where
  (_polyVars, t1)   = splitForAllTys t0
  (predTys, t)      = splitPredTys t1
  (args, targ)      = splitFunTys t
  numberOfArguments = length args

  interp :: Int -> Type -> Maybe (NatTransData NatTransContext ConstantFunctor)
  interp i argTy =
    let
      (argSfs, argInner) =
        splitSyntacticFunctors argTy
      cf =
        case argInner of
          TyConApp tc [] ->
            ConstantFunctorTyCon tc
          TyVarTy v ->
            ConstantFunctorTyVar v
          _ ->
            error "interp: Impossible"
    in
    checkSource (argSfs, cf) >>| \from ->
      NatTransData
      { name
      , context = map WrappedType predTys
      , from
      , to = natTransTo
      , functorArgumentPosition = i
      , numberOfArguments
      }

  natTransTo = Word targSfs targEndCap

  checkSource :: ([SyntacticFunctor], ConstantFunctor) -> Maybe (Word SyntacticFunctor ConstantFunctor)

  targEndCap :: Maybe ConstantFunctor
  (targEndCap, checkSource) =
    case targInner of
      TyVarTy v ->
        let
          targVarOccursInArgs args =
            v `elementOfUniqSet` tyVarsOfTypes (map unwrapType args)
        in
        if v `elementOfUniqSet` nonParametricTypes
        then 
          ( Just (ConstantFunctorTyVar v)
          , \(sfs, inner) ->
              Just (Word sfs (Just inner))
          )
        else
          ( Nothing
          , \(sfs, inner) ->
              if any (\(_f, args) -> targVarOccursInArgs args) sfs
              then Nothing
              else
                case inner of
                  ConstantFunctorTyVar v' ->
                    if v' == v
                    then Just (Word sfs Nothing)
                    else Just (Word sfs (Just inner))

                  ConstantFunctorTyCon tc ->
                    Just (Word sfs (Just inner))
          )

      TyConApp tc [] ->
        ( Just (ConstantFunctorTyCon tc)
        , \(sfs, inner) ->
            Just (Word sfs (Just inner))
        )

      -- TODO: Impossible cases
      TyConApp _tc (_:_) ->
        error "natTransInterpretations: TyConApp args non-empty"
      AppTy _t _t' ->
        error "natTransInterpretations: AppTy"
      FunTy _t _t' ->
        error "natTransInterpretations: FunTy"
      ForAllTy _v _t ->
        error "natTransInterpretations: ForAllTy"
      LitTy _tl ->
        error "natTransInterpretations: LitTy"

  (targSfs, targInner) = splitSyntacticFunctors targ
  nonParametricTypes   = tyVarsOfTypes predTys

-- TODO: Check that no other arg of targSfs contains the inner poly var
-- TODO: Should disallow transes whose from ConstantFunctor is a tyvar
-- different from the innerpolyvar of the target

-- Currently filters out transformations from/to the identity since the
-- string diagrams stuff for that is currently borked
natTransInterpretationsStrict
  :: Class -> InstEnv.InstEnvs
  -> (Name, Type)
  -> [NatTransData NatTransContext Type]
natTransInterpretationsStrict functorClass instEnvs (name, t0) =
  if Word.isEmpty natTransTo
  then []
  else
    filter isReasonableTrans $ catMaybes (zipWith interp [0..] args)
  where
  (_polyVars, t1)   = splitForAllTys t0
  (predTys, t)      = splitPredTys t1
  (args, targ)      = splitFunTys t
  numberOfArguments = length args

  interp :: Int -> Type -> Maybe (NatTransData NatTransContext Type)
  interp i argTy =
    let
      (argSfs, argInner) =
        splitSyntacticFunctors argTy
      cf =
        case argInner of
          TyConApp tc [] ->
            ConstantFunctorTyCon tc
          TyVarTy v ->
            ConstantFunctorTyVar v
          _ ->
            error "interp: Impossible"
    in
    checkSource (argSfs, cf) >>= \from ->
      let
        nd =
          NatTransData
          { name
          , context = map WrappedType predTys
          , from
          , to = natTransTo
          , functorArgumentPosition = i
          , numberOfArguments
          }
      in
      if Word.isEmpty from then Nothing else Just nd
      -- if hasFunctorialEnds nd then Just nd else Nothing

  natTransTo = Word targSfs targEndCap

  hasFunctorialEnds :: NatTransData NatTransContext Type -> Bool
  hasFunctorialEnds (NatTransData {context, from, to}) =
    isFunctorialWord context from && isFunctorialWord context to

  isFunctorialWord :: NatTransContext -> Word SyntacticFunctor Type -> Bool
  isFunctorialWord ctx (Word fs _inner) =
    all (isFunctor ctx) fs

  isFunctor :: NatTransContext -> SyntacticFunctor -> Bool
  isFunctor (map unwrapType -> ctx) (tyFun, map unwrapType -> args) =
    let
      (matches, unifs, _) = lookupInstEnv instEnvs functorClass [addPredTys ctx joined]
    in
    not (null matches) || not (null unifs)
    where
    joined =
      case tyFun of
        TypeFunctionTyVar v ->
          List.foldl' AppTy (TyVarTy v) args
        TypeFunctionTyCon tc ->
          TyConApp tc args

  checkSource :: ([SyntacticFunctor], ConstantFunctor) -> Maybe (Word SyntacticFunctor Type)

  targEndCap :: Maybe Type
  (targEndCap, checkSource) =
    case targInner of
      TyVarTy v ->
        let
          targVarOccursInArgs args =
            v `elementOfUniqSet` tyVarsOfTypes (map unwrapType args)
        in
        if v `elementOfUniqSet` nonParametricTypes
        then 
          ( Just (TyVarTy v)
          , \(sfs, inner) ->
              let
                innerTyMay =
                  case inner of
                    ConstantFunctorTyVar v' ->
                      if v' `elementOfUniqSet` nonParametricTypes
                      then Just (TyVarTy v')
                      else Nothing
                    ConstantFunctorTyCon tc ->
                      Just (TyConApp tc [])
              in
              Just (Word sfs innerTyMay)
          )
        else
          ( Nothing
          , \(sfs, inner) ->
              if any (\(_f, args) -> targVarOccursInArgs args) sfs
              then Nothing
              else
                case inner of
                  ConstantFunctorTyVar v' ->
                    if v' == v
                    then Just (Word sfs Nothing)
                    else Nothing

                  ConstantFunctorTyCon tc ->
                    Just (Word sfs (Just (TyConApp tc [])))
          )

      TyConApp tc [] ->
        ( Just (TyConApp tc [])
        , \(sfs, inner) ->
            let
              innerTyMay =
                case inner of
                  ConstantFunctorTyVar v' ->
                    if v' `elementOfUniqSet` nonParametricTypes
                    then Just (TyVarTy v')
                    else Nothing
                  ConstantFunctorTyCon tc ->
                    Just (TyConApp tc [])
            in
            Just (Word sfs innerTyMay)
        )

      -- TODO: Impossible cases
      TyConApp _tc (_:_) ->
        error "natTransInterpretations: TyConApp args non-empty"
      AppTy _t _t' ->
        error "natTransInterpretations: AppTy"
      FunTy _t _t' ->
        error "natTransInterpretations: FunTy"
      ForAllTy _v _t ->
        error "natTransInterpretations: ForAllTy"
      LitTy _tl ->
        error "natTransInterpretations: LitTy"

  (targSfs, targInner) = splitSyntacticFunctors targ
  nonParametricTypes   = tyVarsOfTypes predTys
splitSyntacticFunctors :: Type -> ([SyntacticFunctor], Type)
splitSyntacticFunctors t =
  let
    (f, ts) = splitAppTys t
    (tyFun, preArgs) =
      case f of
        TyVarTy v ->
          (TypeFunctionTyVar v, [])

        TyConApp tc kots ->
          (TypeFunctionTyCon tc, kots)

        FunTy _t _t' ->
          error "splitAppTys': FunTy"
        ForAllTy _v _t ->
          error "splitAppTys': ForAllTy"
        LitTy _tl ->
          error "splitAppTys': LitTy"
        AppTy _t _t' ->
          error "splitAppTys': AppTy"
  in
  case splitLast ts of
    Nothing ->
      -- TODO: This is also assuming that preArgs is empty, which I think
      -- should be the case.
      ([], t)

    Just (ts', t_last) ->
      let (sfs, tyInner) = splitSyntacticFunctors t_last in
      ((tyFun, map WrappedType (preArgs ++ ts')) : sfs, tyInner)

equivalentContexts :: [PredType] -> [PredType] -> Bool
equivalentContexts ctx1 ctx2 =
  case (f ctx1 ctx2, f ctx2 ctx1) of
    (Just _, Just _) -> True
    _ -> False
  where
  f x y =
    Unify.tcMatchTys (Type.tyVarsOfTypes x) x y

splitLast :: [a] -> Maybe ([a], a)
splitLast [] = Nothing
splitLast xs = Just (splitLast' xs)
  where
  splitLast' :: [a] -> ([a], a)
  splitLast' [x]    = ([], x)
  splitLast' (x:xs) = first (x:) (splitLast' xs)
  splitLast' _      = error "Mote.Search.splitLast': Impossible"

closedSubstNatTransData
  :: Type.TvSubst
  -> NatTransData context Type
  -> Maybe (NatTransData () Type)
closedSubstNatTransData subst nd =
  liftA2 (\from' to' ->
    nd { context = (), from = from', to = to' })
    (substWord subst (from nd))
    (substWord subst (to nd))
  where
    
substSyntacticFunctor subst (tyFun, args) =
  case tyFun of
    TypeFunctionTyCon tc ->
      (TypeFunctionTyCon tc, map (WrappedType . Type.substTy subst . unwrapType) args)

    TypeFunctionTyVar v ->
      let (f, args') = splitAppTys (Type.substTy subst (TyVarTy v)) in
      case f of
        TyVarTy v' ->
          (TypeFunctionTyVar v', map WrappedType args' ++ args)

        TyConApp tc [] ->
          (TypeFunctionTyCon tc, map WrappedType args' ++ args)

        _ ->
          error "substSyntacticFunctor: Impossible case"


substWord subst (Word sfs inner) =
  case inner of
    Nothing ->
      Just (Word (map (substSyntacticFunctor subst) sfs) Nothing)
    Just ty ->
      let (sfs', inner') = splitSyntacticFunctors (Type.substTy subst ty) in
      case inner' of
        TyVarTy _ ->
          Nothing
        _ ->
          Just (Word (map (substSyntacticFunctor subst) sfs ++ sfs') (Just inner'))

    


{-
substWord :: Type.TvSubst -> Word SyntacticFunctor Type -> Word SyntacticFunctor Type
substWord subst (Word fs inner) =
  case inner of

  let (sfs, inner') = splitSyntacticFunctors _
  in
 -}

  {-
  bimap
    (bimap
      (\tyFun -> case tyFun of { TypeFunctionTyVar v -> _; _ -> tyFun })
      (map (WrappedType . Type.substTy subst . unwrapType)))
    (Type.substTy subst) -}

groupAllBy :: (a -> a -> Bool) -> [a] -> [(a, [a])]
groupAllBy f xs =
  case xs of
    [] -> []
    x : xs' ->
      let (grp, xs'') = List.partition (f x) xs' in
      (x, grp) : groupAllBy f xs''

x i r = do
  LoadFile.loadFile r "Foo.hs"

  v <- lift $ newTyVar
  hsc_env <- lift getSession

  typedNames <- fmap catMaybes . mapM (\n -> fmap (n,) <$> nameType n) =<< lift getNamesInScope
  (_messages, Just instEnvs) <- liftIO (runTcInteractive hsc_env TcEnv.tcGetInstEnvs)
  let
    classes =
      map (\inst -> InstEnv.is_cls inst) (InstEnv.instEnvElts (InstEnv.ie_global instEnvs))
    Just functorClass =
      List.find (\cls -> Class.className cls == PrelNames.functorClassName) classes

  let interps = concatMap (natTransInterpretationsStrict functorClass instEnvs) typedNames

  let conv = id

  let thingies =
        map (\(repr, nds) ->
          ( repr
          , nds
          , moreSpecificMonomorphizedSubsts instEnvs
              (map unwrapType (context repr))
          ))
        . groupAllBy (equivalentContexts `on` (map unwrapType . context)) $ interps

      stuff =
        concatMap (\(repr, nds, substs) ->
          let
            reprContext = map unwrapType (context repr)
          in
          concatMap (\nd ->
            let
              ndContext = map unwrapType (context nd)
              Just ndToRepr =
                Unify.tcMatchTys (Type.tyVarsOfTypes ndContext) ndContext reprContext
            in
            mapMaybe
              (\subst0 ->
                let subst = compose ndToRepr subst0 in
                closedSubstNatTransData subst nd >>| \nd' ->
                  (subst, nd, WrappedType (uncontextualizedFromType id nd' v), [nd']))
              substs)
            nds)
          thingies

  -- let (subst, nd0, fromTy, [nd1]) =


{-
  lift . output . map (\(nd, substs) -> let t = (uncontextualizedFromType conv nd v) in(t, context nd, map
    (\subst -> Type.substTy subst t)
    substs))  $ thingies -}
  -- liftIO . print . zipWith const [0..] . snd . (!! i) $ thingies
  -- lift . output $ acceptableSubst wtf

  lift . output . length . List.nubBy equivalentContexts . List.map (map unwrapType) . Set.toList $
    Set.fromList (map context interps)
  liftIO . print . map fst . zip [(0::Int)..] $ stuff
{-

  lift . output . length . map (\subst -> Type.substTy subst (uncontextualizedFromType conv someInterp v)) $
    moreSpecificMonomorphizedSubsts instEnvs
      (map unwrapType (context someInterp))

  lift . output . length $
    monomorphizings instEnvs
      (map unwrapType (context someInterp), uncontextualizedFromType (\x -> case x of
        ConstantFunctorTyVar v -> TyVarTy v
        ConstantFunctorTyCon tc -> TyConApp tc []) someInterp v)

  lift . forM_ (zip [(0::Int)..] interps) $ \(i, interp) -> do
    output $ (i, interp)
    output . map (\subst -> Type.substTy subst (uncontextualizedFromType conv interp v)) . take 100 $
      moreSpecificMonomorphizedSubsts instEnvs
        (map unwrapType (context interp)) -}

      {-
      monomorphizings instEnvs
        (map unwrapType (context interp), uncontextualizedFromType (\x -> case x of
          ConstantFunctorTyVar v -> TyVarTy v
          ConstantFunctorTyCon tc -> TyConApp tc []) interp v) -}

{-
  liftIO $ print (length interps)
  lift $ output $ zip [(0::Int)..] (map name someInterps)


  unifs <- lift . fmap (map (\(_,unifs,_) -> unifs)) $ f (map unwrapType (context someInterp))
  lift $ output (name someInterp, context someInterp, unifs)
  liftIO $ print "coming soon"
  lift $ output $ (someInterp, moreSpecificContexts instEnvs (map unwrapType (context someInterp))) -}


newTyVar :: (GhcMonad m) => m Var
newTyVar = do
  hsc_env <- getSession
  fmap (\(_errs, Just v) -> v) . liftIO . runTcInteractive hsc_env $ do
    uniq <- newUnique
    return $
      mkGlobalVar
        VanillaId
        (mkInternalName uniq (mkVarOcc "yadummy") noSrcSpan)
        liftedTypeKind
          vanillaIdInfo

compareFromTypes
  :: WrappedType -- NatTransData NatTransContext ConstantFunctor
  -> WrappedType -- NatTransData NatTransContext ConstantFunctor
  -> M (Maybe Ordering)
compareFromTypes (WrappedType t1_0) (WrappedType t2_0) = do
  -- TODO: Not sure if it's kosher to get one "v" like this.
  hsc_env0 <- lift getSession
  let
    hsc_env =
      hsc_env0 { hsc_dflags = hsc_dflags hsc_env0 `DynFlags.gopt_unset` DynFlags.Opt_DeferTypeErrors }
--  v <- lift newTyVar

  let 
    tyVars =
      UniqSet.uniqSetToList (tyVarsOfTypes [t1_0, t2_0])
    t1 = mkForAllTys tyVars t1_0
    t2 = mkForAllTys tyVars t2_0

  (_messages, may1) <- liftIO . runTcInteractive hsc_env $
    subTypeEvTc t1 t2
  (_messages, may2) <- liftIO . runTcInteractive hsc_env $
    subTypeEvTc t2 t1

  return $ case (may1, may2) of
    (Just _, Nothing) ->
      Just LT
    (Nothing, Just _) ->
      Just GT
    (Just _, Just _) ->
      Just EQ
    (Nothing, Nothing) ->
      Nothing

monomorphizings
  :: InstEnv.InstEnvs
  -> ([PredType], Type)
  -> [Type]
monomorphizings instEnvs (predTys0, ty0) = go 2 predTys0 ty0
  where
  -- We're as productive as possible
  go 0 _ _ = []
  go fuel predTys ty =
    let
      contextsAndSubsts =
        moreSpecificContexts instEnvs predTys

      (readyToGo, keepCooking) =
        List.partition (\(predTys',_) -> List.null predTys') $ contextsAndSubsts
    in
    List.map (\(_, subst) -> Type.substTy subst ty) readyToGo
    ++ concatMap (\(predTys, subst) -> go (fuel - 1) predTys (Type.substTy subst ty)) keepCooking

{- TODO: Do something like this if efficiency turns out to be an issue
makeMoreSpecificMonomorphizedSubsts
  :: (MonadState (Set.Set [WrappedType]) m)
  => InstEnv.InstEnv
  -> [PredType]
  -> m ()
makeMoreSpecificMonomorphizedSubsts instEnvs predTys =
  go 2 Type.emptyTvSubst
-}

moreSpecificMonomorphizedSubsts
  :: InstEnv.InstEnvs
  -> [PredType]
  -> [Type.TvSubst]
moreSpecificMonomorphizedSubsts instEnvs predTys0 = go' 2 Type.emptyTvSubst predTys0
  where
  -- Eq just balloons too fast
  acceptableContext = all acceptablePredType

  acceptablePredType :: PredType -> Bool
  acceptablePredType predTy =
    let (cls, _) = Type.getClassPredTys predTy in
    Class.className cls /= PrelNames.eqClassName
    && Class.className cls /= PrelNames.ordClassName

  go' :: Int -> Type.TvSubst -> [PredType] -> [Type.TvSubst]
  go' 0 _ _ = []
  go' fuel subst predTys
    | acceptableContext predTys =
      case predTys of
        [] ->
          [subst]

        _ ->
          let
            contextsAndSubsts =
              moreSpecificContexts instEnvs predTys
            (readyToGo, keepCooking) =
              List.partition (null . fst) contextsAndSubsts
          in
          mapMaybe (\(_, subst') -> 
            let subst'' = compose subst subst' in
            if acceptableSubst subst''
            then Just subst''
            else Nothing)
            readyToGo
          ++
          List.concatMap (\(predTys', subst') ->
            let subst'' = compose subst subst' in
            if acceptableSubst subst''
            then go' (fuel - 1) subst'' predTys'
            else [])
            contextsAndSubsts
    | otherwise =
      []

{-
  go :: Int -> Type.TvSubst -> [PredType] -> [Type.TvSubst]
  go 0 _ _ = []
  go fuel subst predTys =
    if acceptableSubst subst
    then 
      let
        contextsAndSubsts =
          moreSpecificContexts instEnvs predTys
        (readyToGo, keepCooking) =
          List.partition (\(predTys',_) -> List.null predTys') $ contextsAndSubsts
      in
      List.map (\(_, subst') ->
        compose subst subst')
        readyToGo
      ++
      concatMap (\(predTys', subst') ->
        go (fuel - 1) (compose subst subst') predTys')
        keepCooking
    else
      [] -}

compose subst subst' =
  let
    inScope = Type.getTvInScope subst'
  in
  Type.mkTvSubst inScope
    (Type.composeTvSubst
      inScope
      (Type.getTvSubstEnv subst')
      (Type.getTvSubstEnv subst))

moreSpecificContexts
  :: InstEnv.InstEnvs
  -> [PredType]
  -> [ ([PredType], Type.TvSubst) ]
moreSpecificContexts instEnvs predTys =
  let
    substses0 =
      map (\predTy ->
        let
          (cls, args) =
            Type.getClassPredTys predTy
          (matches, unifs, _) =
            lookupInstEnv instEnvs cls args
        in
        unifs)
        predTys
  in
  map (first (concatMap instConstraints)) $ go Type.emptyTvSubst substses0
  where
  uniquesToVars :: UniqFM.UniqFM Var
  uniquesToVars = tyVarsOfTypes predTys

  instConstraints :: ClsInst -> [PredType]
  instConstraints inst =
    let
      dfun =
        InstEnv.is_dfun inst
      (_tvs, theta0, _res_ty) =
        TcType.tcSplitSigmaTy (idType dfun)
      theta =
        drop (Id.dfunNSilent dfun) theta0
    in
    theta

  go :: Type.TvSubst -> [ [(ClsInst, TvSubst)] ]  -> [ ([ClsInst], Type.TvSubst) ]
  go commitments [] = [ ([], commitments) ]
  go commitments (substsForCls : substses) =
    concatMap (\(inst1, subst1) ->
      case extendMany commitments subst1 of
        Nothing ->
          []

        Just commitments' ->
          map (first (inst1 :))
            (go commitments' substses))
      substsForCls
    where
    extendMany :: Type.TvSubst -> Type.TvSubst -> Maybe Type.TvSubst
    extendMany subst0 subst_new =
      let
        maySubstEnv' =
          loop (Type.getTvSubstEnv subst0)
            (mapMaybe
              (\(u, ty) -> (,ty) <$> UniqFM.lookupUFM_Directly uniquesToVars u)
              (UniqFM.ufmToList (Type.getTvSubstEnv subst_new)))
      in
      Type.mkTvSubst
        (VarEnv.unionInScope
          (Type.getTvInScope subst0)
          (Type.getTvInScope subst_new))
      <$> maySubstEnv'
      where
      loop substEnv [] =
        Just substEnv

      loop substEnv ((var, ty) : bindings) =
        extendEnv substEnv var ty >>= \substEnv' ->
        loop substEnv' bindings

acceptableSubst :: Type.TvSubst -> Bool
acceptableSubst subst =
  UniqFM.foldUFM (\t b -> let x = not (isUndesirableType t) in {-trace ("desirables=" ++ show x)-} (x && b))
    True
    (Type.getTvSubstEnv subst)

isUndesirableType :: Type -> Bool
isUndesirableType t0 =
  case t0 of
    TyConApp tc kots ->
      let name = nameToString (getName tc) in
      tyConArity tc > 3
      || (TyCon.isTupleTyCon tc && hasTrivialUnitArg kots)
      || any isUndesirableType kots
      || name == "Proxy"
      || name == "Const"

    AppTy t t' ->
      isUndesirableType t || isUndesirableType t'

    FunTy t t' ->
      isUndesirableType t || isUndesirableType t'

    ForAllTy v t ->
      isUndesirableType t

    _ ->
      False

  where
  hasTrivialUnitArg args =
    case args of
      [] ->
        False
      _ ->
        any (\case {TyConApp tc _ -> getUnique tc == PrelNames.unitTyConKey; _ -> False})
          args

moreSpecificPredecessors
  :: InstEnv.InstEnvs
  -> WrappedType
  -> _ -- [WrappedType]
moreSpecificPredecessors instEnvs (WrappedType ty0) =
  let
    (predTys, ty) = splitPredTys ty0

    {- Too complicated for now.
    substsByVarSubsts =
      map
        (List.foldl'
          (\m (_inst, subst) ->
            let substPairs = UniqFM.ufmToList $ Type.getTvSubstEnv subst in
            _
            )
          Map.empty)
        substses
    -}
  in
          -- (cls, args) = Type.getClassPredTys predTy
  moreSpecificContexts instEnvs predTys

-- Checks if t1 is as general as t2
match :: Type -> Type -> Maybe Type.TvSubst
match t1_0 t2_0 =
  let
    t1 = Type.dropForAlls t1_0
    t2 = Type.dropForAlls t2_0
  in
  Unify.tcMatchTy
    (Type.tyVarsOfType t1)
    t1
    t2

-- It's very possible that the "above" pointers get broken. That's not so
-- bad since "below" is what we really care about, but they do need to be
-- fixed before finding minimal elements
{-
addMoreSpecificPredecessorsToPoset
  :: (WrappedType, [WrappedType])
  -> PurePoset.PosetStore WrappedType [NatTransContext]
  -> PurePoset.PosetStore WrappedType [NatTransContext]
addMoreSpecificPredecessorsToPoset (ty, specTys) poset0 =
  List.foldl' (\poset specTy ->
    Map.alter (\case
      Just ed ->
        Just (ed { ElementData.below = Set.insert ty (ElementData.below ed) })
      Nothing ->
        Just (ElementData.ElementData
        { above = Set.empty
        , below = Set.singleton ty
        , value = []
        }))
      specTy
      poset)
    poset0
    specTys
  {-
  mapM_ (\specTy ->
    HashTable.lookup poset specTy >>= \case
      Just ed ->
        HashTable.insert poset specTy (ed { ElementData.below = _ })
      Nothing -> _)
    specTys -}
-}

-- For a given [PredType], want all substitutions which simultaneously
-- satisfy all constraints. I.e., given [r_1,...,r_n] want a substitution \sigma
-- and a new context [s_1,....,s_k] such that
-- such that (s_1,...s_k) => we have instances \sigma(r_1),...,\sigma(r_n)
-- (MonadError e m) => m a
-- ~> [((Monad m', Error e), m := ErrorT e m'), ((), m := Either e)]
-- f :: (GhcMonad m) => [PredType] -> m [InstEnv.ClsInstLookupResult]
f predTys = do
  hsc_env <- getSession
  (_messages, Just instEnvs) <- liftIO (runTcInteractive hsc_env TcEnv.tcGetInstEnvs)
  let
    lookupResults =
      map (\t ->
        let (c, ts) = Type.getClassPredTys t in
        lookupInstEnv instEnvs c ts)
        predTys

  return lookupResults

contextualizedFromType
  :: NatTransData NatTransContext ConstantFunctor
  -> (Var -> Type)
contextualizedFromType (NatTransData {context, from}) innerVar =
  let
    Word fs inner = from
    withoutContext =
      stitchUp fs
        (maybe
          (TyVarTy innerVar)
          (\case 
              ConstantFunctorTyCon tc ->
                TyConApp tc []
              ConstantFunctorTyVar v ->
                -- TODO: Should I remove this from universally quantified vars in the compare function?
                TyVarTy v)
          inner)
    usedTyVars = tyVarsOfType withoutContext
  in
  addPredTys
    (filter
      (\t ->
        let tvs = tyVarsOfType t in
        UniqSet.sizeUniqSet
          (UniqSet.intersectUniqSets tvs usedTyVars)
          ==
          UniqSet.sizeUniqSet tvs)
      (map unwrapType context))
    withoutContext
  where
  stitchUp fs innerTy =
    case fs of
      [] ->
        innerTy
      (tyFun, map unwrapType -> args) : fs' ->
        case tyFun of
          TypeFunctionTyVar v ->
            AppTy 
              (foldl
                (\r arg -> AppTy r arg)
                (TyVarTy v)
                args)
              (stitchUp fs' innerTy)

          TypeFunctionTyCon tc ->
            if isFunTyCon tc
            then
              let [arg] = args in
              FunTy arg (stitchUp fs' innerTy)
            else
              TyConApp tc
                (args ++ [stitchUp fs' innerTy])


type Map = Map.Map -- TODO: Switch to IntMap for performance
data ElementData
  = ElementData
  { above :: Map WrappedType Type.TvSubst -- More specific types
  -- , below :: Map WrappedType Type.TvSubst
  , natTranses :: HashMap.HashMap (Int, Int) (NatTransData () Type) -- transes keyed by their name and functorArgumentPosition
  }

typePoset ::
  Var -- A fresh var which we apply the from-type-functors to
  -> [(Type, [ NatTransData () Type ])] -- NatTranses by monomorphized pre-cooked from-type
  ->
    Map.Map
      WrappedType -- monomorphized type
      ElementData
typePoset freshVar transesByType =
  let
    addAbove tyBottom tyTop substBottomToTop ndsBottom =
      Map.alter (\case
        Nothing ->
          Just
          (ElementData
          { above = Map.singleton (WrappedType tyTop) substBottomToTop
          , natTranses = transMapFromList ndsBottom
          })

        Just ed ->
          Just
          (ed
          { above = Map.insert (WrappedType tyTop) substBottomToTop (above ed)
          }))
        (WrappedType tyBottom)
  in
  List.foldl'
    (\m ((fromTy1, nds1), (fromTy2, nds2)) ->
      case (match fromTy1 fromTy2, match fromTy2 fromTy1) of
        -- The two are unrelated
        (Nothing, Nothing) ->
          m

        -- fromTy1 is strictly more general than fromTy2
        (Just subst1to2, Nothing) ->
          addAbove fromTy1 fromTy2 subst1to2 nds1 m

        -- fromTy2 is strictly more general than fromTy1
        (Nothing, Just subst2to1) ->
          addAbove fromTy2 fromTy1 subst2to1 nds2 m

        (Just subst1to2, Just subst2to1) ->
          let
            defaultData =
              ElementData Map.empty HashMap.empty
          in
          let
            ElementData {above=above1, natTranses=natTranses1} =
              fromMaybe defaultData (Map.lookup (WrappedType fromTy1) m)
            (fromMaybe defaultData -> ElementData {above=above2,natTranses=natTranses2}, m') = 
              Map.updateLookupWithKey (\_ _ -> Nothing) (WrappedType fromTy2) m
          in
          Map.insert
            (WrappedType fromTy1)
            (ElementData
            { above = Map.union above1 above2
            , natTranses = HashMap.union natTranses1 natTranses2 
            })
            m')
    Map.empty
    (pairs transesByType)
  where
  transMapFromList =
    HashMap.fromList . map (\nd -> ((getKey (getUnique (name nd)), functorArgumentPosition nd), nd))

  pairs :: [a] -> [(a, a)]
  pairs []     = []
  pairs (x:xs) = map (x,) xs ++ pairs xs


uncontextualizedFromType :: (constant -> Type) -> NatTransData context constant -> Var -> Type
uncontextualizedFromType conv (NatTransData {from = Word fs inner}) freshVar =
  stitchUp fs 
  where
  innerTy =
    maybe (TyVarTy freshVar) conv inner

  stitchUp fs =
    case fs of
      [] ->
        innerTy

      (tyFun, map unwrapType -> args) : fs' ->
        case tyFun of
          TypeFunctionTyVar v ->
            AppTy 
              (foldl
                (\r arg -> AppTy r arg)
                (TyVarTy v)
                args)
              (stitchUp fs')

          TypeFunctionTyCon tc ->
            if isFunTyCon tc
            then
              let [arg] = args in
              FunTy arg (stitchUp fs')
            else
              TyConApp tc
                (args ++ [stitchUp fs'])


nameType :: Name -> M (Maybe Type)
nameType n = do
  hsc_env <- lift getSession
  (_errs, mayTy) <- liftIO $
    runTcInteractive hsc_env . discardConstraints . tcRnExprTc . noLoc . HsVar . Exact $ n
  return $ mayTy

-- Modified from InstEnv.lookupInstEnv' to keep the TvSubsts for unifying
-- instances instead of throwing them away
lookupInstEnv' :: InstEnv.InstEnv          -- InstEnv to look in
               -> InstEnv.VisibleOrphanModules   -- But filter against this
               -> Class -> [Type]  -- What we are looking for
               -> ([InstEnv.InstMatch],    -- Successful matches
                   [(ClsInst, TvSubst)])     -- These don't match but do unify
-- The second component of the result pair happens when we look up
--      Foo [a]
-- in an InstEnv that has entries for
--      Foo [Int]
--      Foo [b]
-- Then which we choose would depend on the way in which 'a'
-- is instantiated.  So we report that Foo [b] is a match (mapping b->a)
-- but Foo [Int] is a unifier.  This gives the caller a better chance of
-- giving a suitable error message

lookupInstEnv' ie vis_mods cls tys
  = lookup ie
  where
    rough_tcs  = InstEnv.roughMatchTcs tys
    all_tvs    = all isNothing rough_tcs
    --------------
    -- No choice but to coerce ClsInstEnv to [ClsInst] since the newtype is
    -- not exposed. Actually can't even write the type.
    lookup env = case UniqFM.lookupUFM env cls of
                   Nothing -> ([],[])   -- No instances for this class
                   -- S
                   Just insts -> find [] [] (Unsafe.Coerce.unsafeCoerce insts)

    --------------
    find ms us [] = (ms, us)
    find ms us (item@(InstEnv.ClsInst { is_tcs = mb_tcs, is_tvs = tpl_tvs
                              , is_tys = tpl_tys, is_flag = oflag }) : rest)
      | not (InstEnv.instIsVisible vis_mods item)
      = find ms us rest  -- See Note [Instance lookup and orphan instances]

        -- Fast check for no match, uses the "rough match" fields
      | InstEnv.instanceCantMatch rough_tcs mb_tcs
      = find ms us rest

      | Just subst <- Unify.tcMatchTys tpl_tv_set tpl_tys tys
      = find ((item, map (lookup_tv subst) tpl_tvs) : ms) us rest

        -- Does not match, so next check whether the things unify
        -- See Note [Overlapping instances] and Note [Incoherent instances]
      | InstEnv.Incoherent _ <- InstEnv.overlapMode oflag
      = find ms us rest

      | otherwise
      =         -- Unification will break badly if the variables overlap
                -- They shouldn't because we allocate separate uniques for them
                -- See Note [Template tyvars are fresh]
        case Unify.tcUnifyTys InstEnv.instanceBindFun tpl_tys tys of
            Just subst -> find ms ((item, subst):us) rest
            Nothing    -> find ms us        rest
      where
        tpl_tv_set = VarSet.mkVarSet tpl_tvs

    ----------------
    lookup_tv :: TvSubst -> TyVar -> InstEnv.DFunInstType
        -- See Note [DFunInstType: instantiating types]
    lookup_tv subst tv = case Type.lookupTyVar subst tv of
                                Just ty -> Just ty
                                Nothing -> Nothing


---------------
-- This is the common way to call this function.
lookupInstEnv :: InstEnv.InstEnvs     -- External and home package inst-env
              -> Class -> [Type]   -- What we are looking for
              -> ([(ClsInst, [InstEnv.DFunInstType])], [(ClsInst, TvSubst)], Bool)
-- ^ See Note [Rules for instance lookup]
lookupInstEnv (InstEnv.InstEnvs { ie_global = pkg_ie, ie_local = home_ie, ie_visible = vis_mods }) cls tys
  = (final_matches, final_unifs, safe_fail)
  where
    (home_matches, home_unifs) = lookupInstEnv' home_ie vis_mods cls tys
    (pkg_matches,  pkg_unifs)  = lookupInstEnv' pkg_ie  vis_mods cls tys
    all_matches = home_matches ++ pkg_matches
    all_unifs   = home_unifs   ++ pkg_unifs
    pruned_matches = foldr insert_overlapping [] all_matches
        -- Even if the unifs is non-empty (an error situation)
        -- we still prune the matches, so that the error message isn't
        -- misleading (complaining of multiple matches when some should be
        -- overlapped away)

    (final_matches, safe_fail)
       = case pruned_matches of
           [match] -> check_safe match all_matches
           _       -> (pruned_matches, False)

    -- If the selected match is incoherent, discard all unifiers
    final_unifs = case final_matches of
                    (m:_) | is_incoherent m -> []
                    _ -> all_unifs

    -- NOTE [Safe Haskell isSafeOverlap]
    -- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    -- We restrict code compiled in 'Safe' mode from overriding code
    -- compiled in any other mode. The rationale is that code compiled
    -- in 'Safe' mode is code that is untrusted by the ghc user. So
    -- we shouldn't let that code change the behaviour of code the
    -- user didn't compile in 'Safe' mode since that's the code they
    -- trust. So 'Safe' instances can only overlap instances from the
    -- same module. A same instance origin policy for safe compiled
    -- instances.
    check_safe match@(inst,_) others
        = case InstEnv.isSafeOverlap (InstEnv.is_flag inst) of
                -- most specific isn't from a Safe module so OK
                False -> ([match], False)
                -- otherwise we make sure it only overlaps instances from
                -- the same module
                True -> (go [] others, True)
        where
            go bad [] = match:bad
            go bad (i@(x,_):unchecked) =
                if inSameMod x
                    then go bad unchecked
                    else go (i:bad) unchecked

            inSameMod b =
                let na = getName $ getName inst
                    la = Name.isInternalName na
                    nb = getName $ getName b
                    lb = Name.isInternalName nb
                in (la && lb) || (nameModule na == nameModule nb)
---------------
is_incoherent :: InstEnv.InstMatch -> Bool
is_incoherent (inst, _) = case InstEnv.overlapMode (InstEnv.is_flag inst) of
                            InstEnv.Incoherent _ -> True
                            _            -> False

---------------
insert_overlapping :: InstEnv.InstMatch -> [InstEnv.InstMatch] -> [InstEnv.InstMatch]
-- ^ Add a new solution, knocking out strictly less specific ones
-- See Note [Rules for instance lookup]
insert_overlapping new_item [] = [new_item]
insert_overlapping new_item (old_item : old_items)
  | new_beats_old        -- New strictly overrides old
  , not old_beats_new
  , new_item `can_override` old_item
  = insert_overlapping new_item old_items

  | old_beats_new        -- Old strictly overrides new
  , not new_beats_old
  , old_item `can_override` new_item
  = old_item : old_items

  -- Discard incoherent instances; see Note [Incoherent instances]
  | is_incoherent old_item       -- Old is incoherent; discard it
  = insert_overlapping new_item old_items
  | is_incoherent new_item       -- New is incoherent; discard it
  = old_item : old_items

  -- Equal or incomparable, and neither is incoherent; keep both
  | otherwise
  = old_item : insert_overlapping new_item old_items
  where

    new_beats_old = new_item `more_specific_than` old_item
    old_beats_new = old_item `more_specific_than` new_item

    -- `instB` can be instantiated to match `instA`
    -- or the two are equal
    (instA,_) `more_specific_than` (instB,_)
      = isJust (Unify.tcMatchTys (VarSet.mkVarSet (InstEnv.is_tvs instB))
               (InstEnv.is_tys instB) (InstEnv.is_tys instA))

    (instA, _) `can_override` (instB, _)
       =  BasicTypes.hasOverlappingFlag  (BasicTypes.overlapMode (InstEnv.is_flag instA))
       || BasicTypes.hasOverlappableFlag (BasicTypes.overlapMode (InstEnv.is_flag instB))
       -- Overlap permitted if either the more specific instance
       -- is marked as overlapping, or the more general one is
       -- marked as overlappable.
       -- Latest change described in: Trac #9242.
       -- Previous change: Trac #3877, Dec 10.

extendEnv :: Type.TvSubstEnv -> Var -> Type -> Maybe Type.TvSubstEnv
extendEnv subst v ty =
  Cloned.Unify.tcUnifyTyExtending subst (TyVarTy v) ty -- Unify.tcUnifyTyWithSubst subst (TyVarTy v) ty
