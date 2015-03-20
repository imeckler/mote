{-# LANGUAGE FlexibleContexts, LambdaCase, MultiParamTypeClasses,
             NamedFieldPuns, RecordWildCards #-}
module Slick.Refine where

import           Control.Applicative ((<$>))
import           Control.Monad.Error (ErrorT (..), MonadError, lift, throwError)
import           Control.Monad.Trans (MonadIO, MonadTrans)
import           Data.IORef          (IORef)
import qualified Data.Set            as S
import           GhcMonad
import           HsExpr              (HsExpr (..), LHsExpr)
import           OccName             (mkVarOcc, occName)
import           RdrName             (RdrName (Unqual))
import           SrcLoc              (noLoc, noSrcSpan, unLoc)
import           TcRnDriver          (runTcInteractive)
import           TcRnTypes           (CtOrigin (..))
import           TcType              (TcSigmaType)
import           Type                (dropForAlls, mkForAllTys, splitForAllTys,
                                      splitFunTy_maybe, mkPiTypes)
import           TypeRep             (Type)

import           Slick.GhcUtil
import           Slick.ReadType
import           Slick.Types
import           Slick.Util
import Slick.Holes

-- Imports for doing subtype testing
import           Data.Either         (rights)
import           Name                (mkInternalName)
import           Parser              (parseType)
import           RnTypes             (extractHsTysRdrTyVars)
import           TcEvidence          (EvBind (..), EvTerm (..))
import TcExpr (tcInferRho)
import           TcRnMonad           (captureConstraints, newUnique, failIfErrsM)
import           TcSimplify          (simplifyInteractive)
import           TcType              (UserTypeCtxt (GhciCtxt))
import           TcUnify             (tcSubType)
import PrelNames (itName)
import RnExpr (rnLExpr)
import SrcLoc (getLoc)
import TcSimplify (simplifyInfer)
import TcMType (zonkTcType)
import TcRnMonad


tcRnExprTc :: LHsExpr RdrName -> TcRn Type
tcRnExprTc rdr_expr = do
  (rn_expr, _fvs) <- rnLExpr rdr_expr
  failIfErrsM
  uniq <- newUnique
  let fresh_it = itName uniq (getLoc rdr_expr)
  -- I guess I could pick up some new holes here, but there's really no
  -- point since in general we might have to load after a refine.
  ((_tc_expr, res_ty), lie) <- captureConstraints $ tcInferRho rn_expr
  ((qtvs, dicts, _, _), lie_top) <- captureConstraints $
    simplifyInfer True False [(fresh_it, res_ty)] lie
  simplifyInteractive lie_top
  zonkTcType . mkForAllTys qtvs $ mkPiTypes dicts res_ty

refineExpr
  :: Num b => IORef SlickState -> Type -> LHsExpr RdrName -> ErrorT ErrorType Ghc b
refineExpr stRef goalTy e = do
  ty <- hsExprType e
  refineType stRef goalTy ty

refineType
  :: (MonadError ErrorType (t m), MonadTrans t, GhcMonad m,
      MonadIO (t m), Num b) =>
     IORef SlickState -> Type -> Type -> t m b
refineType stRef goalTy t = let (tyVars, t') = splitForAllTys t in go 0 tyVars t'
-- foralls of the argument type t should get pushed down as we go
  where
  -- The subtype thing doesn't play nice with polymorphism.
  -- If we have a hole _ :: a (not forall a. a, it's a specific type
  -- variable) and refine with fromJust :: forall t. Maybe t -> t,
  -- subType says that a < the type of fromJust and we just stick fromJust
  -- in the hole.
  go acc tyVars t =
    let (tyVars', t') = splitForAllTys t
        tyVars'' = tyVars ++ tyVars'
    in
    do
      tyStr <- lift (showPprM (goalTy, mkForAllTys tyVars'' t))
      logS stRef $ "refineType: " ++ tyStr
      -- TODO: check what subtype does on (dropForAlls <$> readType "a") and
      -- (dropForAlls <$> readType "a")
      lift (subType goalTy (mkForAllTys tyVars'' t)) >>= \case
        True  -> return acc
        False -> case splitFunTy_maybe t' of
          Nothing      -> throwError NoRefine
          Just (_, t'') -> go (1 + acc) tyVars'' t''

refine :: IORef SlickState -> String -> M (LHsExpr RdrName)
refine stRef eStr = do
  h     <- getCurrentHoleErr stRef
  isArg <- S.member h . argHoles <$> gReadIORef stRef
  hi    <- getCurrentHoleInfoErr stRef
  -- got rid of dropForAlls here, but that's definitely wrong as per const
  -- example
  --
  -- first order approximation: just instantiate all abstracted
  -- kindvars to *. I believe this is approximately correct since
  -- if there were real constraints on the kinds (ignoring prescribed type
  -- signature), they would have been put in the result of readType
  --
  -- this is complicated...

  (gbl_env, _) <- tm_internals_ . typecheckedModule <$> gReadIORef stRef
  let goalTy  = holeType hi
      lcl_env = ctLocEnv . ctLoc $ holeCt hi

  expr <- parseExpr eStr
  hsc_env <- lift getSession

  runTcInteractive hsc_env $
    setEnvs (gbl_env, lcl_env) $ do
      rty <- tcRnExprTc expr
      n   <- go 0 [] goalTy rty
  where
  go acc tyVars goalTy rty = do
    let (tyVars', rty') = splitForAllTys rty
        tyVars''        = tyVars ++ tyVars'
    subTypeTc goalTy (mkForAllTys tyVars'' rty') >>= \case
      True -> return (Just acc)
      False -> case splitFunTy_maybe rty' of
        Nothing         -> return Nothing
        Just (_, rty'') -> go (1 + acc) tyVars'' rty''


  -- have to make sure that the hole-local type variables are in scope
  -- for "withBindings"
  {-
  ErrorT . withBindings holeEnv . runErrorT $ do
    expr' <- refineToExpr stRef goalTy =<< parseExpr eStr
    let atomic =
          case unLoc expr' of
            HsVar {}     -> True
            HsIPVar {}   -> True
            HsOverLit {} -> True
            HsLit {}     -> True
            HsPar {}     -> True
            _            -> False
    return $ if isArg && not atomic then noLoc (HsPar expr') else expr'
-}
refineToExpr
  :: IORef SlickState
     -> Type
     -> LHsExpr RdrName
     -> M (LHsExpr RdrName)
refineToExpr stRef goalTy e =
  refineExpr stRef goalTy e >>| \argsNum -> withNHoles argsNum e

withNHoles :: Int -> LHsExpr RdrName -> LHsExpr RdrName
withNHoles n e = app e $ replicate n hole where
  app f args = foldl (\f' x -> noLoc $ HsApp f' x) f args
  hole       = noLoc $ HsVar (Unqual (mkVarOcc "_"))

{-
holeRdrTyVars :: GhcMonad m => HoleInfo -> m [RdrName]
holeRdrTyVars (HoleInfo {holeEnv}) = do
  hsTys <- fmap rights . mapM (runParserM parseType) $ map snd holeEnv
  let (_rdrKvs, rdrTvs) = extractHsTysRdrTyVars hsTys
  return rdrTvs

subTypeEvInHole hi t1 t2 = do
  env <- getSession
  rdrTvs <- holeRdrTyVars hi
  fmap snd . liftIO . runTcInteractive env $ do
    nameTvs <- mapM toNameVar rdrTvs
    withTyVarsInScope nameTvs $ do
      (_, cons) <- captureConstraints (tcSubType origin ctx t1 t2)
      simplifyInteractive cons
  where
  toNameVar x = do { u <- newUnique; return $ Name.mkInternalName u (occName x) noSrcSpan }
  origin = AmbigOrigin GhciCtxt
  ctx = GhciCtxt
-}

subTypeEvTc t1 t2 = do
  { (_, cons) <- captureConstraints (tcSubType origin ctx t1 t2)
  ; simplifyInteractive cons }
  where
  origin = AmbigOrigin GhciCtxt
  ctx = GhciCtxt

subTypeTc t1 t2 = do
  b <- subTypeEvTc t1 t2 
  allBag (\(EvBind _ t) -> case t of
    EvDelayedError {} -> False
    _                 -> True) b

subTypeEv t1 t2 = do
  { env <- getSession
  ; fmap snd . liftIO . runTcInteractive env $ subTypeEvTc t1 t2 }

subType t1 t2 =
  subTypeEv t1 t2 >>| \case
    Nothing -> False
    Just b  -> allBag (\(EvBind _ t) -> case t of
      EvDelayedError{} -> False
      _                -> True) b
