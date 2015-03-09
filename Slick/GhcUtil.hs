{-# LANGUAGE LambdaCase #-}
module Slick.GhcUtil where

import           Bag                 (Bag, foldrBag)
import           Control.Monad       ((<=<))
import           Control.Monad.Error (lift, throwError)
import           ErrUtils            (pprErrMsgBag)
import qualified GHC
import           GhcMonad            (GhcMonad, getSession, getSessionDynFlags,
                                      setSession)
import           HsExpr              (HsExpr (HsVar), LHsExpr, StmtLR (BodyStmt))
import           Outputable          (showSDoc, vcat)
import           Parser              (parseStmt)
import           RdrName             (RdrName (Exact))
import           SrcLoc
import           TcEvidence
import           TcRnDriver          (tcRnExpr)
import           TcRnMonad
import           TcSimplify
import           TcType              (UserTypeCtxt (GhciCtxt), TcSigmaType)
import           TcUnify             (tcSubType)
import           Type

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

subTypeEv
  :: GhcMonad m => TcSigmaType -> TcSigmaType -> m (Maybe (Bag EvBind))
subTypeEv t1 t2 = do
  { env <- getSession
  ; fmap snd . liftIO . GHC.runTcInteractive env $ do
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

allBag :: (a -> Bool) -> Bag a -> Bool
allBag p = foldrBag (\x r -> if p x then r else False) True

nameVar :: GHC.Name -> Located (HsExpr RdrName)
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
  mapM_ (\b -> GHC.runStmt (mkBind b) GHC.RunToCompletion) bs
  x <- mx
  setSession env0 -- this is maybe a little violent...
  return x
  where
  mkBind (x, t) = "let " ++ x ++ " = undefined :: " ++ t

