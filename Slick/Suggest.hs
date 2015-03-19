{-# LANGUAGE TupleSections, LambdaCase #-}
module Suggest where

import GhcMonad
import GHC
import GhcUtil
import Type
import RdrName
import Util
import HsExpr
import Control.Applicative
import Data.Maybe
import GhcUtil
import Refine
import OccName

mapMaybeM f = fmap catMaybes . mapM f

eitherToMaybe = either (const Nothing) Just

getScope :: GhcMonad m => m [(Name, Type)]
getScope = getNamesInScope >>=
  mapMaybeM (\n ->
    fmap (fmap (n,) . eitherToMaybe)
      (hsExprType (nameVar n)))

suggestions :: GhcMonad m => Type -> m [LHsExpr RdrName]
suggestions goal = do
  scope <- getScope
  flip mapMaybeM scope $ \(n, t) ->
    refineType goal t >>| \case
      Just k  -> Just $ withNHoles (nameVar n) k
      Nothing -> Nothing

