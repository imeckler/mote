{-# LANGUAGE FlexibleContexts, LambdaCase, MultiParamTypeClasses,
             NamedFieldPuns, RecordWildCards #-}
module Slick.Refine where

import           Control.Applicative ((<$>))
import           Control.Monad.Error (ErrorT (..), MonadError, lift, throwError)
import           Outputable          (showSDoc, vcat)
import           Control.Monad.Trans (MonadIO, MonadTrans)
import           ErrUtils            (pprErrMsgBag)
import           Data.IORef          (IORef)
import qualified Data.Set            as S
import           GhcMonad
import GHC (TypecheckedModule(..))
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

refine :: IORef SlickState -> String -> M (LHsExpr RdrName)
refine stRef eStr = do
  logS stRef "refine1"
  h     <- getCurrentHoleErr stRef
  isArg <- S.member h . argHoles <$> gReadIORef stRef
  hi    <- getCurrentHoleInfoErr stRef
  logS stRef "refine2"
  -- got rid of dropForAlls here, but that's definitely wrong as per const
  -- example
  fs <- lift getSessionDynFlags
  let goalTy            = holeType hi
      go acc tyVars rty = do
        logS stRef $ showType fs rty
        let (tyVars', rty') = splitForAllTys rty
            tyVars'' = tyVars ++ tyVars'

        logS stRef $ "rty: " ++ showType fs rty
        logS stRef $ "rty': " ++ showType fs rty'

        logS stRef $ "comparing: " ++ showType fs goalTy
        logS stRef $ "with: " ++ showType fs (mkForAllTys tyVars'' rty)
        subTypeTc (mkForAllTys tyVars'' rty) goalTy >>= \case
          True -> return (Right acc)
          False -> case splitFunTy_maybe rty' of
            Nothing        -> return (Left NoRefine)
            Just (_, rty'') -> go (1 + acc) tyVars'' rty''

  expr <- parseExpr eStr
  (nerr, _cons) <- inHoleEnv stRef . captureConstraints $ do
    rty <- tcRnExprTc expr
    logS stRef $ showType fs rty
    go 0 [] rty
  {-
  (gbl_env, _) <- tm_internals_ . typecheckedModule <$> getFileDataErr stRef
      lcl_env = ctLocEnv . ctLoc $ holeCt hi

  hsc_env <- lift getSession

  ((_warns, errs), nerrMay) <- liftIO . runTcInteractive hsc_env $
    setEnvs (gbl_env, lcl_env) $ do
      rty <- tcRnExprTc expr
      go 0 [] goalTy rty
  fs   <- lift getSessionDynFlags
  nerr <- maybe (throwErrs fs errs) return nerrMay
  -}
  logS stRef "refine3"
  case nerr of
    Right n  -> return $ withNHoles n expr
    Left err -> throwError err
  
  where

--    let (tyVars', rty') = splitForAllTys rty
--        tyVars''        = tyVars ++ tyVars'

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

withNHoles :: Int -> LHsExpr RdrName -> LHsExpr RdrName
withNHoles n e = app e $ replicate n hole where
  app f args = foldl (\f' x -> noLoc $ HsApp f' x) f args
  hole       = noLoc $ HsVar (Unqual (mkVarOcc "_"))


subTypeEvTc t1 t2 = do
  { (_, cons) <- captureConstraints (tcSubType origin ctx t1 t2)
  ; simplifyInteractive cons }
  where
  origin = AmbigOrigin GhciCtxt
  ctx = GhciCtxt

subTypeTc t1 t2 =
  subTypeEvTc t1 t2 >>|
    allBag (\(EvBind _ t) -> case t of
      EvDelayedError {} -> False
      _                 -> True)

