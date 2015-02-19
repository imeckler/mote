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
import GhcUtil

import Panic

-- refine :: Type -> String -> Either String Int

-- refine' :: Type -> HsExpr RdrName ->

-- exprType :: GhcMonad m => String -> Either String Type

refineExpr goalTy e = do
  ty_orerr <- exprType e
  fmap (\case {Just x -> Right x; _ -> Left "Couldn't refine"} =<<)
    (traverse (refineType goalTy) ty_orerr)

refineType goalTy = go 0
  where
  go :: GhcMonad m => Int -> Type -> m (Maybe Int)
  go acc t = subType goalTy t >>= \case
    True  -> return (Just acc)
    False -> case splitFunTy_maybe t of
      Nothing      -> return Nothing
      Just (_, t') -> go (1 + acc) t'

