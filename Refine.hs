{-# LANGUAGE LambdaCase #-}
module Refine where

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

import Panic

-- refine :: Type -> String -> Either String Int

-- refine' :: Type -> HsExpr RdrName ->

-- exprType :: GhcMonad m => String -> Either String Type

exprType e = do
  hsc_env <- getSession
  fs <- getSessionDynFlags
  parseExpr e >>= \case
    Left err -> return (Left err)
    Right expr -> do
      ((warns, errs), mayTy) <- liftIO $ tcRnExpr hsc_env expr
      return $ case mayTy of 
        Just t -> Right t
        Nothing -> Left (showSDoc fs . vcat $ pprErrMsgBag errs)
    
parseExpr e = do
  stmt_orerr <- runParserM parseStmt e
  return $ stmt_orerr >>= \case
    Just (L _ (BodyStmt expr _ _ _)) -> Right expr
    _                                -> Left "Expected body statement"

subType goal t = do
  hsc_env <- getSession
  id $
    liftIO (runTcInteractive hsc_env $ tcSubType origin ctxt t goal) >>| \case
      (_, Just _)  -> True
      (_, Nothing) -> False
  where
  ctxt = GhciCtxt
  origin = AmbigOrigin GhciCtxt

refine goalTy e = do
  ty_orerr <- exprType e
  fmap (\case {Just x -> Right x; _ -> Left "Couldn't refine"} =<<)
    (traverse (go 0) ty_orerr)
  where
  go :: GhcMonad m => Int -> Type -> m (Maybe Int)
  go acc t = subType goalTy t >>= \case
    True  -> return (Just acc)
    False -> case splitFunTy_maybe t of
      Nothing      -> return Nothing
      Just (_, t') -> go (1 + acc) t'

