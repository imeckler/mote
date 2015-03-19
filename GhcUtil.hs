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
import TcRnTypes
import Type
import TcRnMonad
import Bag
import RdrName
import Name
import SrcLoc
import Types
import Control.Monad.Error
-- TODO: DEBUG IMPORTS
import Parser (parseType)

exprType :: String -> M Type
exprType = hsExprType <=< parseExpr

hsExprType :: LHsExpr RdrName -> M Type
hsExprType expr = do
  hsc_env <- lift getSession
  fs      <- lift getSessionDynFlags
  ((warns, errs), mayTy) <- liftIO $ tcRnExpr hsc_env expr
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


-- TcRnMonad.newUnique
-- RnTypes.filterInScope has clues
--   put RdrName of relevant tyvars into LocalRdrEnv
--   RdrName.elemLocalRdrEnv
--   extendLocalRdrEnv

-- for debugging
withStrTyVarsInScope = withTyVarsInScope

-- should actually use  TcEnv/tcExtendTyVarEnv. I doubt this will work as is.
-- looks like I want RnEnv/bindLocatedLocals
withTyVarsInScope :: [Name] -> TcRn a -> TcRn a
withTyVarsInScope tvNames inner = do
  lcl_rdr_env <- TcRnMonad.getLocalRdrEnv
  TcRnMonad.setLocalRdrEnv
    (RdrName.extendLocalRdrEnvList lcl_rdr_env tvNames)
    inner

withTyVarsInScope' :: [Name] -> TcRn a -> TcRn a
withTyVarsInScope' tvNames inner = do
-- check out
-- RnTypes/bindHsTyVars

rdrNameToName rdrName = do
  u <- newUnique
  return $ Name.mkSystemName u (occName rdrName)


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

