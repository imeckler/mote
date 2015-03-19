{-# LANGUAGE LambdaCase, RecordWildCards #-}
module Slick.GhcUtil where

import           Bag                 (Bag, foldrBag)
import           Control.Monad.Error
import           ErrUtils            (pprErrMsgBag)
import           GHC                 hiding (exprType)
import           Name
import           Outputable          (showSDoc, vcat)
import           Parser              (parseStmt)
import           RdrName             (RdrName (Exact), extendLocalRdrEnvList)
import           SrcLoc              (realSrcSpanEnd, realSrcSpanStart)
import           TcRnDriver          (tcRnExpr)
import           TcRnMonad

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

-- TcRnMonad.newUnique
-- RnTypes.filterInScope has clues
--   put RdrName of relevant tyvars into LocalRdrEnv
--   RdrName.elemLocalRdrEnv
--   extendLocalRdrEnv

-- for debugging
withStrTyVarsInScope :: [Name] -> TcRn a -> TcRn a
withStrTyVarsInScope = withTyVarsInScope

-- should actually use  TcEnv/tcExtendTyVarEnv. I doubt this will work as is.
-- looks like I want RnEnv/bindLocatedLocals
withTyVarsInScope :: [Name] -> TcRn a -> TcRn a
withTyVarsInScope tvNames inner = do
  lcl_rdr_env <- TcRnMonad.getLocalRdrEnv
  TcRnMonad.setLocalRdrEnv
    (extendLocalRdrEnvList lcl_rdr_env tvNames)
    inner

{-
withTyVarsInScope' :: [Name] -> TcRn a -> TcRn a
withTyVarsInScope' tvNames inner = do
-- check out
-- RnTypes/bindHsTyVars
-}

rdrNameToName :: HasOccName name => name -> IOEnv (Env gbl lcl) Name
rdrNameToName rdrName = do
  u <- newUnique
  return $ Name.mkSystemName u (occName rdrName)

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

