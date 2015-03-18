{-# LANGUAGE LambdaCase, RecordWildCards #-}
module GhcUtil where

import Parser (parseStmt)
import Util
import HsExpr
import GhcMonad
import GHC hiding (exprType)
import Outputable (vcat, showSDoc)
import ErrUtils (pprErrMsgBag)
import TcRnDriver (tcRnExpr)
import TcUnify (tcSubType)
import TcRnTypes
import TcType (UserTypeCtxt(GhciCtxt))
import Type
import TcSimplify
import TcRnMonad
import TcEvidence
import Bag
import RdrName
import Name
import SrcLoc
import Types
import Control.Monad.Error
-- TODO: DEBUG IMPORTS
import RnTypes
import Parser (parseType)
import Data.Either (rights)

exprType :: String -> M Type
exprType = hsExprType <=< parseExpr

hsExprType :: LHsExpr RdrName -> M Type
hsExprType expr = do
  hsc_env <- lift getSession
  fs      <- lift getSessionDynFlags
  ((warns, errs), mayTy) <- liftIO $ tcRnExpr hsc_env expr
  case mayTy of 
    Just t  -> return t
    Nothing -> throwError . showSDoc fs . vcat $ pprErrMsgBag errs
   
parseExpr :: String -> M (LHsExpr RdrName)
parseExpr e = do
  stmt_orerr <- lift $ runParserM parseStmt e
  eitherThrow stmt_orerr >>= \case
    Just (L _ (BodyStmt expr _ _ _)) -> return expr
    _                                -> throwError "Expected body statement"

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

-- TcRnMonad.newUnique
-- RnTypes.filterInScope has clues
--   put RdrName of relevant tyvars into LocalRdrEnv
--   RdrName.elemLocalRdrEnv
--   extendLocalRdrEnv

-- for debugging
withStrTyVarsInScope = withTyVarsInScope

withTyVarsInScope :: [Name] -> TcRn a -> TcRn a
withTyVarsInScope tvNames inner = do
  lcl_rdr_env <- TcRnMonad.getLocalRdrEnv
  TcRnMonad.setLocalRdrEnv
    (RdrName.extendLocalRdrEnvList lcl_rdr_env tvNames)
    inner

rdrNameToName rdrName = do
  u <- newUnique
  return $ Name.mkSystemName u (occName rdrName)


tyVarTest = do
  Right hsTy <- runParserM parseType "a" :: Ghc (Either String (LHsType RdrName))
  return $ extractHsTyRdrTyVars hsTy


allBag p = foldrBag (\x r -> if p x then r else False) True

nameVar = noLoc . HsVar . Exact

toSpan (RealSrcSpan rss) =
  (toPos (realSrcSpanStart rss), toPos (realSrcSpanEnd rss))

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

