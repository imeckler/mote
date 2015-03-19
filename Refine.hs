{-# LANGUAGE LambdaCase, RecordWildCards, NamedFieldPuns #-}
module Refine where

import Control.Applicative
import Parser (parseStmt)
import Util
import HsExpr
import GhcMonad
import GHC hiding (exprType)
import Outputable (vcat, showSDoc)
import ErrUtils (pprErrMsgBag)
import TcRnTypes
import TcType (UserTypeCtxt(GhciCtxt))
import Type
import GhcUtil
import OccName
import Control.Monad.Error
import Types
import Data.IORef (IORef)
import ReadType
import qualified Data.Set as S

-- Imports for doing subtype testing
import TcUnify (tcSubType)
import TcType (UserTypeCtxt(GhciCtxt))
import TcEvidence (EvBind(..), EvTerm(..))
import TcSimplify (simplifyInteractive)
import Data.Either (rights)
import TcRnMonad (newUnique, captureConstraints)
import RnTypes (extractHsTysRdrTyVars)
import Parser (parseType)
import Name (mkInternalName)

import Panic

refineExpr stRef goalTy e = do
  ty <- hsExprType e
  refineType stRef goalTy ty

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

refineToExpr stRef goalTy e =
  refineExpr stRef goalTy e >>| \argsNum -> withNHoles argsNum e

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
