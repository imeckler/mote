{-# LANGUAGE LambdaCase #-}
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
import Data.Traversable
import TcRnTypes
import TcType (UserTypeCtxt(GhciCtxt))
import Type
import TcSimplify
import TcRnMonad
import TcEvidence
import Bag
import RdrName
import SrcLoc
import Types
import Control.Monad.Error

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

