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
                                      splitFunTy_maybe)
import           TypeRep             (Type)

import           Slick.GhcUtil
import           Slick.ReadType
import           Slick.Types
import           Slick.Util

-- Imports for doing subtype testing
import           Data.Either         (rights)
import           Name                (mkInternalName)
import           Parser              (parseType)
import           RnTypes             (extractHsTysRdrTyVars)
import           TcEvidence          (EvBind (..), EvTerm (..))
import           TcRnMonad           (captureConstraints, newUnique)
import           TcSimplify          (simplifyInteractive)
import           TcType              (UserTypeCtxt (GhciCtxt))
import           TcUnify             (tcSubType)

refineExpr
  :: Num b => IORef SlickState -> TcSigmaType -> LHsExpr RdrName -> ErrorT ErrorType Ghc b
refineExpr stRef goalTy e = do
  ty <- hsExprType e
  refineType stRef goalTy ty

refineType
  :: (MonadError ErrorType (t m), MonadTrans t, GhcMonad m,
      MonadIO (t m), Num b) =>
     IORef SlickState -> TcSigmaType -> Type -> t m b
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
  h                  <- getCurrentHoleErr stRef
  isArg              <- S.member h . argHoles <$> gReadIORef stRef
  hi@(HoleInfo {..}) <- getCurrentHoleInfoErr stRef
  -- got rid of dropForAlls here, but that's definitely wrong as per const
  -- example
  --
  -- first order approximation: just instantiate all abstracted
  -- kindvars to *. I believe this is approximately correct since
  -- if there were real constraints on the kinds (ignoring prescribed type
  -- signature), they would have been put in the result of readType
  --
  -- this is complicated...
  rdrTyVars <- lift (holeRdrTyVars hi)
  goalTy    <- dropForAlls <$> readType holeTypeStr

  -- have to make sure that the hole-local type variables are in scope
  -- for "withBindings"
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

refineToExpr
  :: IORef SlickState
     -> TcSigmaType
     -> LHsExpr RdrName
     -> ErrorT ErrorType Ghc (LHsExpr RdrName)
refineToExpr stRef goalTy e =
  refineExpr stRef goalTy e >>| \argsNum -> withNHoles argsNum e

withNHoles :: Int -> LHsExpr RdrName -> LHsExpr RdrName
withNHoles n e = app e $ replicate n hole where
  app f args = foldl (\f' x -> noLoc $ HsApp f' x) f args
  hole       = noLoc $ HsVar (Unqual (mkVarOcc "_"))

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


subTypeEv t1 t2 = do
  { env <- getSession
  ; fmap snd . liftIO . runTcInteractive env $ do
  { (_, cons) <- captureConstraints (tcSubType origin ctx t1 t2)
  ; simplifyInteractive cons } }
  where
  origin = AmbigOrigin GhciCtxt
  ctx = GhciCtxt

subType t1 t2 =
  subTypeEv t1 t2 >>| \case
    Nothing -> False
    Just b  -> allBag (\(EvBind _ t) -> case t of
      EvDelayedError{} -> False
      _                -> True) b
