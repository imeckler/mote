{-# LANGUAGE FlexibleContexts, LambdaCase, MultiParamTypeClasses,
             NamedFieldPuns, RecordWildCards, TupleSections #-}
module Slick.Refine where

import           Bag                 (bagToList)
import           Control.Applicative ((<$>))
import           Control.Monad.Error (ErrorT (..), MonadError, lift, throwError)
import           Control.Monad.Trans (MonadIO, MonadTrans)
import           Data.IORef          (IORef)
import qualified Data.Set            as S
import           ErrUtils            (pprErrMsgBag)
import           GHC                 (TypecheckedModule (..))
import           GhcMonad
import           HsExpr              (HsExpr (..), LHsExpr)
import           OccName             (mkVarOcc, occName)
import           Outputable          (showSDoc, vcat)
import           RdrName             (RdrName (Unqual))
import           SrcLoc              (noLoc, noSrcSpan, unLoc)
import           TcRnDriver          (runTcInteractive)
import           TcRnTypes           (CtOrigin (..))
import           TcType              (TcSigmaType)
import           Type                (PredType, TyVar, dropForAlls, isPredTy,
                                      mkForAllTys, mkPiTypes, splitForAllTys,
                                      splitFunTy_maybe)
import           TypeRep             (Type (..))

import           Slick.GhcUtil
import           Slick.Holes
import           Slick.ReadType
import           Slick.Types
import           Slick.Util

-- Imports for doing subtype testing
import           Data.Either         (rights)
import           Name                (mkInternalName)
import           Parser              (parseType)
import           PrelNames           (itName)
import           RnExpr              (rnLExpr)
import           RnTypes             (extractHsTysRdrTyVars)
import           SrcLoc              (getLoc)
import           TcEvidence          (EvBind (..), EvTerm (..), HsWrapper (..))
import           TcExpr              (tcInferRho)
import           TcMType             (zonkTcType)
import           TcRnMonad           (captureConstraints, failIfErrsM,
                                      newUnique)
import           TcRnMonad
import           TcSimplify          (simplifyInteractive)
import           TcSimplify          (simplifyInfer)
import           TcType              (UserTypeCtxt (GhciCtxt))
import           TcUnify             (tcSubType)

-- tcRnExprTc :: LHsExpr RdrName -> TcRn Type
tcRnExprTc rdr_expr = do
  (rn_expr, _fvs) <- rnLExpr rdr_expr
  uniq <- newUnique
  let fresh_it = itName uniq (getLoc rdr_expr)
  -- I guess I could pick up some new holes here, but there's really no
  -- point since in general we might have to load after a refine.
  ((_tc_expr, res_ty), lie) <- captureConstraints $ tcInferRho rn_expr
  ((qtvs, dicts, _, _), lie_top) <- captureConstraints $
    simplifyInfer True False [(fresh_it, res_ty)] lie
  simplifyInteractive lie_top
  zonkTcType . mkForAllTys qtvs $ mkPiTypes dicts res_ty

data RefineMatch = RefineMatch
  { refineForAllVars :: [TyVar]
  , refinePredTys    :: [PredType]
  , refineArgTys     :: [Type]
  , refineTarget     :: Type
  , refineEvBinds    :: [EvBind]
  , refineWrapper    :: HsWrapper
  }

-- score :: RefineMatch -> Int
-- score (RefineMatch {..}) = 

refineMatch :: Type -> Type -> TcRn (Maybe RefineMatch)
refineMatch goalTy rty = go [] [] [] rty where
  go tyVars predTys argTys rty = do
    let (tyVars', rty')   = splitForAllTys rty
        (predTys', rty'') = splitPredTys rty'
        tyVars''          = tyVars ++ tyVars'
        predTys''         = predTys ++ predTys'

    (wrapper, b) <- subTypeEvTc (mkForAllTys tyVars'' $ withArgTys predTys'' rty) goalTy
    case allBag (\(EvBind _ t) -> case t of {EvDelayedError {} -> False; _ -> True}) b of
      True -> return . Just $
        RefineMatch
        { refineForAllVars = tyVars''
        , refinePredTys    = predTys''
        , refineTarget     = rty''
        , refineArgTys     = reverse argTys
        , refineEvBinds    = bagToList b
        , refineWrapper    = wrapper
        }

      False -> case splitFunTy_maybe rty'' of
        Nothing            -> return Nothing
        Just (arg, rty''') -> go tyVars'' predTys'' (arg : argTys) rty'''

  withArgTys ts t = foldr (\s r -> FunTy s r) t ts

refineNumArgs :: Type -> Type -> TcRn (Maybe Int)
refineNumArgs goalTy rty = fmap (length . refineArgTys) <$> refineMatch goalTy rty

-- TODO: If the return type doesn't match, assume it's in the
-- middle of a composition. Eg., if the user tries to refine with f
-- and the type of f doesn't match, insert 
-- _ $ f _ _ _ 
-- for the number of args f has
refine :: Ref SlickState -> String -> M (LHsExpr RdrName)
refine stRef eStr = do
  hi    <- holeInfo <$> getCurrentHoleErr stRef
  isArg <- S.member (holeSpan hi) . argHoles <$> gReadRef stRef
  fs    <- lift getSessionDynFlags
  let goalTy = holeType hi

  expr <- parseExpr eStr
  tcmod <- typecheckedModule <$> getFileDataErr stRef
  (nerr, _cons) <- inHoleEnv tcmod hi . captureConstraints $ do
    rty <- tcRnExprTc expr
    refineNumArgs goalTy rty

  case nerr of
    Just n  ->
      let expr' = withNHoles n expr
          atomic =
            case unLoc expr' of
              HsVar {}     -> True
              HsIPVar {}   -> True
              HsOverLit {} -> True
              HsLit {}     -> True
              HsPar {}     -> True
              EWildPat     -> True
              _            -> False
      in
      return $ if isArg && not atomic then noLoc (HsPar expr') else expr'

    Nothing -> throwError NoRefine


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

-- TODO: There's a bug where goal type [a_a2qhr] doesn't accept refinement
-- type [HoleInfo]
-- TODO: Refinement for record constructors
subTypeEvTc t1 t2 = do
  { (wrapper, cons) <- captureConstraints (tcSubType origin ctx t1 t2)
  ; (wrapper,) <$> simplifyInteractive cons }
  where
  origin = AmbigOrigin GhciCtxt
  ctx = GhciCtxt

