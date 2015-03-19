{-# LANGUAGE LambdaCase, RecordWildCards #-}
module Slick.GhcUtil where

import           Bag                 (Bag, foldrBag)
import           Control.Monad       ((<=<))
import           Control.Monad.Error (lift, throwError)
import           ErrUtils            (pprErrMsgBag)
import           GHC                 hiding (exprType)
import           Name
import           Outputable          (showSDoc, vcat)
import           Parser              (parseStmt)
import           RdrName             (RdrName (Exact), extendLocalRdrEnvList)
import           SrcLoc              (realSrcSpanStart, realSrcSpanEnd)
import           TcEvidence
import           TcRnDriver          (tcRnExpr)
import           TcRnMonad
import           TcSimplify
import           TcType              (TcSigmaType, UserTypeCtxt (GhciCtxt))
import           TcUnify             (tcSubType)

import           Data.Either         (rights)
import           Parser              (parseType)
import           RnTypes

import           Slick.Types
import           Slick.Util

exprType :: String -> M Type
exprType = hsExprType <=< parseExpr

hsExprType :: LHsExpr RdrName -> M Type
hsExprType expr = do
  hsc_env <- lift getSession
  fs      <- lift getSessionDynFlags
  ((_warns, errs), mayTy) <- liftIO $ tcRnExpr hsc_env expr
  case mayTy of
    Just t  -> return t
    Nothing -> throwError . GHCError . showSDoc fs . vcat $ pprErrMsgBag errs

parseExpr :: String -> M (LHsExpr RdrName)
parseExpr e = lift (runParserM parseStmt e) >>= \case
  Right (Just (L _ (BodyStmt expr _ _ _))) ->
    return expr
  Right _                                  ->
    throwError $ ParseError "Expected body statement."
  Left parseError ->
    throwError $ ParseError parseError

subTypeEvInHole
  :: GhcMonad m =>
     HoleInfo -> TcSigmaType -> TcSigmaType -> m (Maybe (Bag EvBind))
subTypeEvInHole (HoleInfo {..}) t1 t2 = do
  hsTys <- fmap rights . mapM (runParserM parseType) $ map snd holeEnv
  let (_rdrKvs, rdrTvs) = extractHsTysRdrTyVars hsTys
  env <- getSession
  fmap snd . liftIO . runTcInteractive env $ do
    nameTvs <- mapM toNameVar rdrTvs
    withTyVarsInScope nameTvs $ do
      (_, cons) <- captureConstraints (tcSubType origin ctx t1 t2)
      simplifyInteractive cons
  where
  toNameVar x = do { u <- newUnique; return $ Name.mkInternalName u (occName x) noSrcSpan }
  origin = AmbigOrigin GhciCtxt
  ctx = GhciCtxt

subTypeEv
  :: GhcMonad m => TcSigmaType -> TcSigmaType -> m (Maybe (Bag EvBind))
subTypeEv t1 t2 = do
  { env <- getSession
  ; fmap snd . liftIO . runTcInteractive env $ do
  { (_, cons) <- captureConstraints (tcSubType origin ctx t1 t2)
  ; simplifyInteractive cons } }
  where
  origin = AmbigOrigin GhciCtxt
  ctx = GhciCtxt

subType :: GhcMonad f => TcSigmaType -> TcSigmaType -> f Bool
subType t1 t2 =
  subTypeEv t1 t2 >>| \case
    Nothing -> False
    Just b  -> allBag (\(EvBind _ t) -> case t of
      EvDelayedError{} -> False
      _                -> True) b

-- TcRnMonad.newUnique
-- RnTypes.filterInScope has clues
--   put RdrName of relevant tyvars into LocalRdrEnv
--   RdrName.elemLocalRdrEnv
--   extendLocalRdrEnv

-- for debugging
withStrTyVarsInScope :: [Name] -> TcRn a -> TcRn a
withStrTyVarsInScope = withTyVarsInScope

withTyVarsInScope :: [Name] -> TcRn a -> TcRn a
withTyVarsInScope tvNames inner = do
  lcl_rdr_env <- TcRnMonad.getLocalRdrEnv
  TcRnMonad.setLocalRdrEnv
    (extendLocalRdrEnvList lcl_rdr_env tvNames)
    inner

rdrNameToName :: HasOccName name => name -> IOEnv (Env gbl lcl) Name
rdrNameToName rdrName = do
  u <- newUnique
  return $ Name.mkSystemName u (occName rdrName)

tyVarTest = do
  Right hsTy <- runParserM parseType "a" :: Ghc (Either String (LHsType RdrName))
  return $ extractHsTyRdrTyVars hsTy

allBag :: (a -> Bool) -> Bag a -> Bool
allBag p = foldrBag (\x r -> if p x then r else False) True

nameVar :: Name -> Located (HsExpr RdrName)
nameVar = noLoc . HsVar . Exact

toSpan :: SrcSpan -> ((Int, Int), (Int, Int))
toSpan (RealSrcSpan rss) =
  (toPos (realSrcSpanStart rss), toPos (realSrcSpanEnd rss))
toSpan UnhelpfulSpan {} = error "Unhelpful span."

toPos :: RealSrcLoc -> (Int, Int)
toPos rsl = (srcLocLine rsl, srcLocCol rsl)

-- needed for refine and the real version of getting hole env

-- (var, Type)
withBindings :: GhcMonad m => [(String, String)] -> m a -> m a
withBindings bs mx = do
  env0 <- getSession
  mapM_ (\b -> runStmt (mkBind b) RunToCompletion) bs
  x <- mx
  setSession env0 -- this is maybe a little violent...
  return x
  where
  mkBind (x, t) = "let " ++ x ++ " = undefined :: " ++ t

