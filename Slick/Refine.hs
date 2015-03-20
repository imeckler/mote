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
                                      splitFunTy_maybe, mkPiTypes, isPredTy)
import           TypeRep             (Type(..))

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
  h     <- getCurrentHoleErr stRef
  isArg <- S.member h . argHoles <$> gReadIORef stRef
  hi    <- getCurrentHoleInfoErr stRef
  -- got rid of dropForAlls here, but that's definitely wrong as per const
  -- example
  fs <- lift getSessionDynFlags
  let goalTy            = holeType hi
      go acc tyVars predTys rty = do
        let (tyVars', rty')   = splitForAllTys rty
            (predTys', rty'') = splitPredTys rty'
            tyVars''          = tyVars ++ tyVars'
            predTys''         = predTys ++ predTys'

        subTypeTc (mkForAllTys tyVars'' $ withArgTys predTys'' rty) goalTy >>= \case
          True -> return (Right acc)
          False -> case splitFunTy_maybe rty'' of
            Nothing          -> return (Left NoRefine)
            Just (_, rty''') -> go (1 + acc) tyVars'' predTys'' rty'''

  expr <- parseExpr eStr
  (nerr, _cons) <- inHoleEnv stRef . captureConstraints $ do
    rty <- tcRnExprTc expr
    go 0 [] [] rty

  case nerr of
    Right n  ->
      let expr' = withNHoles n expr
          atomic =
            case unLoc expr' of
              HsVar {}     -> True
              HsIPVar {}   -> True
              HsOverLit {} -> True
              HsLit {}     -> True
              HsPar {}     -> True
              _            -> False
      in
      return $ if isArg && not atomic then noLoc (HsPar expr') else expr'

    Left err -> throwError err

  where withArgTys ts t = foldr (\s r -> FunTy s r) t ts

--    let (tyVars', rty') = splitForAllTys rty
--        tyVars''        = tyVars ++ tyVars'

  -- have to make sure that the hole-local type variables are in scope
  -- for "withBindings"
  {-
  ErrorT . withBindings holeEnv . runErrorT $ do
    expr' <- refineToExpr stRef goalTy =<< parseExpr eStr
-}

withNHoles :: Int -> LHsExpr RdrName -> LHsExpr RdrName
withNHoles n e = app e $ replicate n hole where
  app f args = foldl (\f' x -> noLoc $ HsApp f' x) f args
  hole       = noLoc $ HsVar (Unqual (mkVarOcc "_"))

splitPredTys (FunTy t1 t2) | isPredTy t1 = let (ps, t) = splitPredTys t2 in (t1:ps, t)
splitPredTys t                           = ([], t)

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

