{-# LANGUAGE LambdaCase, NamedFieldPuns, RecordWildCards, TupleSections #-}

module Mote.Search where

import           Mote.GhcUtil        (discardConstraints, splitPredTys)
import           Mote.ReadType
import           Mote.Refine         (tcRnExprTc)
import           Mote.Types
import           Mote.Util
import           Prelude             hiding (Word)
import           Search.Graph        hiding (sequence)
import           Search.Graph.Types
import           Search.Types
import           Search.Types.Word   (Word (..))
import qualified Search.Types.Word   as Word
import Mote.Search.WrappedType

import           Control.Applicative
import           Control.Monad.Error

import           Data.Bifunctor
import           Data.Bitraversable
import           Data.Hashable
import qualified Data.List           as List
import qualified Data.Map            as Map
import           Data.Maybe
import           Data.Monoid
import qualified Data.Set            as Set
import           Data.Traversable    (traverse)

import           GHC
import Class (classOpItems, classTyVars)
import Var (tyVarKind)
import           InstEnv             (ClsInst (..))
import           Name
import           Outputable
import qualified PrelNames
import           RdrName
import qualified TyCon
import           Type                (dropForAlls, splitFunTys)
import           TypeRep
import           UniqSet             (elementOfUniqSet)
import           Unique              (getKey, getUnique)
import Var

import           Debug.Trace

{-
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
-}

-- Write a type t as (A1 * ... * An)F where
-- each Ai and F are functors over a variable x

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

-- TODO: SyntacticFuncs should be bundled with the variables that they're
-- universally quantified over

type SyntacticFunc = (TyCon, [WrappedType])
data TransInterpretation = TransInterpretation
  { numArguments            :: Int
  , functorArgumentPosition :: Int
  , name                    :: Name
  , from                    :: Word SyntacticFunc TyCon
  , to                      :: Word SyntacticFunc TyCon
  }

{-
data Func
  = Syntactic SyntacticFunc
  | Constant TyCon -- This tycon is nullary
  deriving (Eq)
-}

toStringTrans :: Trans SyntacticFunc TyCon -> M (Trans String String)
toStringTrans (Trans {from, to, name}) = do
  from' <- lift (bitraverse showPprM showPprM from)
  to'   <- lift (bitraverse showPprM showPprM to)
  return (Trans {from=from', to=to', name})

data CoarseType
  = SomeVar
  | Type WrappedType
  deriving (Eq, Ord)

-- Heuristically ignore distinctions between all TyVars
-- since comparing types gets complicated with TyVars
type CoarseFunc = (TyCon, [CoarseType])

squint :: SyntacticFunc -> CoarseFunc
squint (tc, ts) = (tc, map squintTy ts) where
  squintTy (WrappedType t) = case t of
    TyVarTy _v     -> SomeVar
    _              -> Type (WrappedType t)

-- Filtering occurs here
transes :: Set.Set CoarseFunc -> (Name, Type) -> [Trans SyntacticFunc TyCon]
transes funcs b = mapMaybe toTrans (transInterpretations b)
  where
  toTrans :: TransInterpretation -> Maybe (Trans SyntacticFunc TyCon)
  toTrans (TransInterpretation {..}) =
    if anyNotAFunctor from || anyNotAFunctor to
    then Nothing
    else if from == to
    then Nothing
    else if numArguments > 3 then Nothing
    else if null (Word.beginning to) && null (Word.beginning from) then Nothing
    -- TODO: Have higher weights for information destroying programs
    else Just (Trans {from, to, name=AnnotatedTerm name' (numArguments - 1) 1})
    where
    ident = occNameString $ occName name
    name' =
      if numArguments == 1 
      then Simple ident 
      else if functorArgumentPosition == numArguments - 1
      then Compound (ident ++ " " ++ underscores (numArguments - 1))
      else Simple ("(\\x -> " ++ ident ++ " " ++ underscores functorArgumentPosition ++ " x " ++ underscores (numArguments - functorArgumentPosition - 1) ++ ")")

    underscores n = unwords $ replicate n "_"

    anyNotAFunctor = Word.fold (\sf b -> not (Set.member (squint sf) funcs) || b) (\_ b -> b) False

traversables :: GhcMonad m => m [SyntacticFunc]
traversables = instancesOneParamFunctorClass PrelNames.traversableClassName

monads :: GhcMonad m => m [SyntacticFunc]
monads = instancesOneParamFunctorClass PrelNames.monadClassName

applicatives :: GhcMonad m => m [SyntacticFunc]
applicatives = instancesOneParamFunctorClass PrelNames.applicativeClassName

functors :: GhcMonad m => m [SyntacticFunc]
functors = instancesOneParamFunctorClass PrelNames.functorClassName

instancesOneParamFunctorClass name =
  getInfo False name >>| \case
    Just (_,_,insts,_) -> mapMaybe (extractUnapplied . head . is_tys) insts
    Nothing            -> []


extractUnapplied :: Type -> Maybe SyntacticFunc
extractUnapplied t = case t of
  TyConApp tc kots ->
    Just (tc, map WrappedType kots)

  AppTy t1 t2 ->
    fmap (\(f, args) -> (f, WrappedType t2 : args)) (extractUnapplied t1)
  -- TODO: In the future, this should extract applications of type
  -- variables
  _                -> Nothing

-- TODO: This type is only for debug purposes
data WrappedTyCon = WrappedTyCon TyCon String
instance Eq WrappedTyCon where
  WrappedTyCon tc _ == WrappedTyCon tc' _ = tc == tc'
instance Ord WrappedTyCon where
  compare (WrappedTyCon x _) (WrappedTyCon y _) = compare x y
instance Hashable WrappedTyCon where
  hashWithSalt s (WrappedTyCon tc _) = s `hashWithSalt` getKey (getUnique tc)
instance Show WrappedTyCon where
  show (WrappedTyCon _ s) = show s

-- search :: Word String String -> Word String String -> Int ->  M [NaturalGraph (Int, Int) (Int, Int)]
search src trg n = do
  fs <- lift getSessionDynFlags
  let renderSyntacticFunc :: SyntacticFunc -> (String, String)
      renderSyntacticFunc (tc, args) = (showSDoc fs (ppr tc), showSDoc fs (ppr args)) -- (getKey (getUnique tc), hash args)

      readAndRenderSyntacticFunc =
        join
        . fmap
          ( maybeThrow (OtherError "Could not parse functor for search")
            . fmap renderSyntacticFunc
            . extractUnapplied . dropForAlls)
        . readType
{-
      renderFunc :: Func -> (Int, Int)
      renderFunc f = case f of
        Syntactic sf -> renderSyntacticFunc sf
        Constant tc  -> renderSyntacticFunc (tc, []) -}

--  let showSyntacticFunc = showSDoc fs . ppr
--  let renderSyntacticFunc sf@(tc, args) = WrappedTyCon tc (showSyntacticFunc sf)

  -- TODO: Check that the kinds make sense
  -- TODO: Be more lenient about what the right String can mean
  src'    <- bitraverse readAndRenderSyntacticFunc readAndRenderSyntacticFunc src
  trg'      <- bitraverse readAndRenderSyntacticFunc readAndRenderSyntacticFunc trg
  -- fmap (fmap renderFunc) (readFuncs trg) -- fmap catMaybes $ mapM (fmap (fmap renderSyntacticFunc . extractUnapplied . dropForAlls) . readType) trg
  transes <- fmap (fmap (bimap renderSyntacticFunc (renderSyntacticFunc . (,[])))) $ transesInScope -- fmap (fmap (fmap renderFunc)) $ transesInScope

  -- TODO: For now don't use transes from or to the identity. Too finicky.
  let transes' = filter (\t -> not (mempty == Search.Types.from t || mempty == Search.Types.to t)) transes
  return $ graphsOfSizeAtMost transes' n src' trg'

{-
readFuncs :: [String] -> M [Func]
readFuncs ss = do
  (ss', sLast) <- maybeThrow (OtherError "Mote.Search.readFuncs: Empty list") (splitLast ss)
  sfs <- mapM readSyntacticFunc ss'

  funcLast <- readLastFunc sLast

  return (map Syntactic sfs ++ [funcLast])
  where
  readSyntacticFunc :: String -> M SyntacticFunc
  readSyntacticFunc s = do
    ty <- dropForAlls <$> readType s
    case ty of
      TyConApp tc kots ->
        let argsRemaining = TyCon.tyConArity tc - length kots in
        if argsRemaining == 1
        then return (tc, map WrappedType kots)
        else throwError (OtherError "Mote.Search.readSyntacticFuncs: All but the last element of the list passed to Mote.Search.search must be of kind * -> *")

      _ ->
        throwError (OtherError "Mote.Search.readSyntacticFuncs: Type had the wrong form")

  readLastFunc :: String -> M Func
  readLastFunc s = do
    ty <- dropForAlls <$> readType s
    case ty of
      TyConApp tc [] ->
        let arity = TyCon.tyConArity tc in
        if arity == 0
        then return (Constant tc)
        else
          fmap Syntactic (readSyntacticFunc s) `catchError` \_ ->
            throwError (OtherError "Mote.Search.readLastFunc: The last type in the list should have kind * or * -> *")

      _ ->
        throwError (OtherError "Mote.Search.readLastFunc: Type had the wrong form")
-}

{-
readFunc :: String -> M Func
readFunc s = do
  ty <- dropForAlls <$> readType
  case ty of
    TyConApp tc args ->
      let n = arity tc
    _                ->
      throwError (OtherError "Type is of the wrong form for search")
-}

type Score = (Int, Int, Int)
score :: (AnnotatedTerm, NaturalGraph f o) -> Score
score (t, g) = (numHoles t, Map.size (digraph g), length $ connectedComponents g)

transesInScope :: M [Trans SyntacticFunc TyCon]
transesInScope = do
  namedTys <- fmap catMaybes . mapM (\n -> fmap (n,) <$> nameType n) =<< lift getNamesInScope
  ts <- lift traversables
  as <- lift applicatives
  ms <- lift monads
  funcSet <- lift $ fmap (Set.fromList . map squint) functors
  let joins     =
        mapMaybe (\m@(tc,_) ->
          if PrelNames.listTyConKey == getUnique tc
          then Nothing
          else
            Just $
              Trans
              { from = Word [m,m] Nothing
              , to   = Word [m] Nothing
              , name = AnnotatedTerm (Simple "join") 0 1
              }
        ) ms
      traverses =
        liftA2 (\t f ->
          Trans
          { from = Word [t,f] Nothing
          , to   = Word [f,t] Nothing
          , name = AnnotatedTerm (Simple "sequenceA") 0 1
          }
        ) ts as
  return $
    concatMap (transes funcSet) namedTys ++ traverses ++ joins

nameType :: Name -> M (Maybe Type)
nameType n = do
  hsc_env <- lift getSession
  (_errs, mayTy) <- liftIO $
    runTcInteractive hsc_env . discardConstraints . tcRnExprTc . noLoc . HsVar . Exact $ n
  return $ mayTy


-- TODO: Turn SyntacticFunc into SyntacticFuncScheme
-- so runErrorT can work
splitSyntancticFuncs :: Type -> ([SyntacticFunc], Type)
splitSyntancticFuncs t = case t of
  TyVarTy _v       -> ([], t)
  FunTy _ _        -> ([], t)
  ForAllTy _v t    -> splitSyntancticFuncs t
  LitTy _          -> ([], t)
  AppTy t _t'      -> ([], t) -- TODO
  TyConApp tc kots -> case splitLast kots of
    Nothing          -> ([], t)
    Just (args, arg) -> first ((tc, map WrappedType args) :) (splitSyntancticFuncs arg)

-- TODO: This is, of course, a first approximation since
-- we assume all TyCons other than (->) are covariant in all
-- arguments.
occursStrictlyPositively :: TyVar -> Type -> Bool
occursStrictlyPositively v = not . bad where
  bad t = case t of
    AppTy t' t''      -> bad t' || bad t''
    TyConApp _tc kots -> any bad kots
    FunTy t' t''      -> occurs t' || bad t''
    ForAllTy _ t'     -> bad t'
    LitTy _tl         -> False
    TyVarTy _v        -> False

  occurs t = case t of
    AppTy t' t''      -> occurs t' || occurs t''
    TyConApp _tc kots -> any occurs kots
    FunTy t' t''      -> occurs t' || occurs t''
    ForAllTy _v t'    -> occurs t'
    LitTy _tl         -> False
    TyVarTy v'        -> v' == v

transInterpretations :: (Name, Type) -> [TransInterpretation]
transInterpretations (n, t0) =
  case targInner of
    TyVarTy targPolyVar ->
      if targPolyVar `elementOfUniqSet` forbiddenVars
      then []
      else if any (not . occursStrictlyPositively targPolyVar) args
      then []
      else catMaybes $ zipWith interp [0..] args
      where
      interp i argty
        | WrappedType inner == WrappedType (TyVarTy targPolyVar) =
          Just $
            TransInterpretation
            { numArguments            = numArguments
            , functorArgumentPosition = i
            , name                    = n
            , from                    = Word sfs Nothing
            , to                      = fsTarg
            }

        -- TODO: Actually require a TyCon type for the constant functor for
        -- now.
        | TyConApp tc [] <- inner =
          Just $
            TransInterpretation
            { numArguments            = numArguments
            , functorArgumentPosition = i
            , name                    = n
            , from                    = Word sfs (Just tc)
            , to                      = fsTarg
            }

        | otherwise = Nothing
        where
        (sfs, inner) = splitSyntancticFuncs argty
        fsTarg       = Word sfsTarg Nothing

    TyConApp targTc [] ->
      catMaybes (zipWith interp [0..] args)
      where
      interp i argTys
        -- TODO: Actually require a TyCon type for the constant functor for
        -- now.
        | TyConApp tc [] <- inner =
          Just $
            TransInterpretation
            { numArguments            = numArguments
            , functorArgumentPosition = i
            , name                    = n
            , from                    = Word sfs (Just tc)
            , to                      = fsTarg
            }

        | TyVarTy v <- inner, not (v `elementOfUniqSet` forbiddenVars) =
          Just $
            TransInterpretation
            { numArguments            = numArguments
            , functorArgumentPosition = i
            , name                    = n
            , from                    = Word sfs Nothing
            , to                      = fsTarg
            }

        | otherwise = Nothing
        where
        (sfs, inner) = splitSyntancticFuncs argTys
        fsTarg       = Word sfsTarg (Just targTc)

    _ -> []
  where
  (_polyVars, t1) = splitForAllTys t0
  (predTys, t)    = splitPredTys t1

  forbiddenVars        = tyVarsOfTypes predTys
  (args, targ)         = splitFunTys t
  (sfsTarg, targInner) = splitSyntancticFuncs targ
  numArguments         = length args


{-
TyConApp IO
  [TyConApp Free
    [ TyConApp "[]" []
    , TyConApp Maybe [TyConApp Int]
    ]
  ]
-}


