{-# LANGUAGE LambdaCase, RecordWildCards #-}
module Refine where

import Control.Applicative
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
import Data.IORef (IORef)
import ReadType
import qualified Data.Set as S

import Panic

-- refine :: Type -> String -> Either String Int

-- refine' :: Type -> HsExpr RdrName ->

-- exprType :: GhcMonad m => String -> Either String Type

refineExpr :: Type -> LHsExpr RdrName -> M Int
refineExpr goalTy e = do
  ty <- hsExprType e
  refineType goalTy ty

refineType :: Type -> Type -> M Int
refineType goalTy = go 0 . dropForAlls
  where
  go acc t = lift (subType goalTy t) >>= \case
    True  -> return acc
    False -> case splitFunTy_maybe t of
      Nothing      -> throwError "Couldn't refine"
      Just (_, t') -> go (1 + acc) t'

refine :: IORef SlickState -> String -> M (LHsExpr RdrName)
refine stRef eStr = do
  h             <- getCurrentHoleErr stRef
  isArg         <- S.member h . argHoles <$> gReadIORef stRef
  HoleInfo {..} <- getCurrentHoleInfoErr stRef
  goalTy        <- readType holeTypeStr
  ErrorT . withBindings holeEnv . runErrorT $ do
    expr' <- refineToExpr goalTy =<< parseExpr eStr
    let atomic = 
          case unLoc expr' of
            HsVar {}     -> True
            HsIPVar {}   -> True
            HsOverLit {} -> True
            HsLit {}     -> True
            HsPar {}     -> True
            _            -> False
    return $ if isArg && not atomic then noLoc (HsPar expr') else expr'

refineToExpr goalTy e =
  refineExpr goalTy e >>| \argsNum -> withNHoles argsNum e

withNHoles n e = app e $ replicate n hole where
  app f args = foldl (\f' x -> noLoc $ HsApp f' x) f args
  hole       = noLoc $ HsVar (Unqual (mkVarOcc "_"))

