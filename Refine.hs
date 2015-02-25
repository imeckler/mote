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
import Data.Traversable
import TcRnTypes
import TcType (UserTypeCtxt(GhciCtxt))
import Type
import GhcUtil
import OccName
import Control.Monad.Error
import Types

import Panic

-- refine :: Type -> String -> Either String Int

-- refine' :: Type -> HsExpr RdrName ->

-- exprType :: GhcMonad m => String -> Either String Type

refineExpr :: Type -> LHsExpr RdrName -> M Int
refineExpr goalTy e = do
  ty <- hsExprType e
  refineType goalTy ty

refineType :: Type -> Type -> M Int
refineType goalTy = go 0
  where
  go acc t = lift (subType goalTy t) >>= \case
    True  -> return acc
    False -> case splitFunTy_maybe t of
      Nothing      -> throwError "Couldn't refine"
      Just (_, t') -> go (1 + acc) t'

refine :: Type -> String -> M (LHsExpr RdrName)
refine goalTy eStr = refineToExpr goalTy =<< parseExpr eStr

refineToExpr goalTy e =
  refineExpr goalTy e >>| \argsNum -> withNHoles argsNum e

withNHoles n e = app e $ replicate n hole where
  app f args = foldl (\f' x -> noLoc $ HsApp f' x) f args
  hole       = noLoc $ HsVar (Unqual (mkVarOcc "_"))

