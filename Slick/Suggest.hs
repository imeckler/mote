{-# LANGUAGE LambdaCase, TupleSections #-}
module Suggest where

import           Control.Applicative
import           Data.Maybe
import           GHC
import           GhcMonad
import           GhcUtil
import           GhcUtil
import           HsExpr
import           OccName
import           RdrName
import           Refine
import           Type
import           Util

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

