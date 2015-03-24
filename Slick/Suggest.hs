{-# LANGUAGE LambdaCase, RecordWildCards, TupleSections,
             NoMonomorphismRestriction #-}
module Slick.Suggest where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Error
import           Data.Function       (on)
import           Data.IORef
import qualified Data.List           as List
import           Data.Maybe
import           Data.Traversable    hiding (forM, mapM, sequence)
import           GHC
import           GhcMonad
import           HsExpr
import           HsExpr
import           RdrName
import           Slick.GhcUtil
import           Slick.Holes
import           Slick.Refine
import           Slick.Types
import           Slick.Util
import           TcRnMonad           (captureConstraints, TcRn)
import           TyCon               (isTupleTyCon)
import           Type
-- TODO: DEBUG
import           Generics.SYB.Text
import           Module              (packageIdString)
import           Name                (isInternalName, nameModule_maybe)
import           Outputable          (ppr, showSDoc, showSDocDebug)
import           TcEvidence          (HsWrapper (..))

eitherToMaybe = either (const Nothing) Just

-- TODO: Penalize for universally quantified variables that appear in the
-- refineTarget. Or rather, 
-- 

-- Think I should order lexicographically.
-- First by specificity, then locality (is this hole local, module local, project
-- local, or from an external package)

-- TODO: If the goal is of function type A -> B, suggest things that take
-- an argument of type A and then we can refine by composition
-- TODO: Suggest things where the goal type appears as a type parameter in
-- some type constructor application

data Locality  = Hole | Module | Project | External deriving (Eq, Ord)
type Score     = (Int, Int, Locality)

vagueness :: RefineMatch -> Int
vagueness (RefineMatch {..}) = go refineWrapper where
  go :: HsWrapper -> Int
  go = \case
    WpCompose x0 x1 -> go x0 + go x1
    WpCast x0       -> 0
    WpEvLam x0      -> 1
    WpEvApp x0      -> 1
    WpTyLam x0      -> 1
    WpTyApp x0      -> 1
    WpLet x0        -> 1
    WpHole          -> 0

-- should really count the number of "hard to get" arg tys,
-- but this spills over into proof search
burdensomeness :: RefineMatch -> Int
burdensomeness (RefineMatch {..}) = length refineArgTys

locality :: Name -> Locality
locality n = case nameModule_maybe n of
  Just mod -> case packageIdString (modulePackageId mod) of
    "main" -> Project
    _      -> External
  Nothing  -> if isInternalName n then Module else External

-- TODO: push foralls in
innerArgs :: Type -> [Type]
innerArgs t = case splitAppTys t of
  (_, [])   -> [t]
  (_, args) -> innerArgs (last args)

{-
innerArgs :: Type -> [Type]
innerArgs t = case splitTyConApp_maybe t of
  Just (tycon, args) ->
    -- would like to recurse over args in which this tycon is functorial
    if isTupleTyCon tycon
    then concatMap innerArgs args
    else maybe [t] innerArgs (lastMay args) -- It's about finding ways to make this descent real
  Nothing -> [t]
  where
  lastMay = \case { [] -> Nothing; xs -> Just (last xs) }
-}
matchInnerArgs :: Type -> Type -> TcRn [RefineMatch]
matchInnerArgs goalTy ty = mapMaybeM (refineMatch goalTy) (innerArgs ty)

score :: Bool -> Type -> Type -> Name -> TcRn (Maybe (Score, (Name, Type)))
score hole goalTy ty n = do
  let loc       = if hole then Hole else locality n
      score' rm = (vagueness rm, burdensomeness rm, loc)

  let attempts = ty : innerArgs ty
      goals    = goalTy : innerArgs goalTy

  fmap (fmap (,(n,ty)) . maximumMay)
    . fmap catMaybes
    $ sequence (liftA2 (\t g -> fmap score' <$> refineMatch g t) attempts goals)
  where
  maximumMay = \case { [] -> Nothing; xs -> Just (maximum xs) }
  
{-
  refineMatch goalTy ty >>= \case
    Nothing -> matchInnerArgs goalTy ty
-}
suggestions :: TypecheckedModule -> HoleInfo -> M [(Name, Type)]
suggestions tcmod hi = do
  gblScope <- lift getNamesInScope
  fs <- lift getSessionDynFlags
  -- not sure if it's stricly necessary to do this in Tc environment of the
  -- hole
  gblSuggestions <- mapMaybeM gblScore gblScope
  lclSuggestions <- inHoleEnv tcmod hi $
    discardConstraints . fmap catMaybes . forM (holeEnv hi) $ \(id, ty) ->
      score True goalTy ty (getName id)

  return
    . map snd
    . List.sortBy (compare `on` fst)
    $ (gblSuggestions ++ lclSuggestions)
  where
  goalTy             = holeType hi
  discardConstraints = fmap fst . captureConstraints
  maybeErr ex        = fmap Just ex `catchError` \_ -> return Nothing
  -- TODO: delete debug fs argument
  gblScore n = fmap join . maybeErr . inHoleEnv tcmod hi . discardConstraints $ do
    ty <- tcRnExprTc . noLoc . HsVar $ Exact n
    score False goalTy ty n
--    refineMatch goalTy ty >>| fmap (\rm ->
--      ((vagueness rm, burdensomeness rm, locality n), (n, ty)))

--      logS stRef (showSDoc fs $ ppr (ty, refineEvBinds))
--      logS stRef . showSDocDebug fs $ ppr refineWrapper
--      logS stRef $ "And the wrapper is " ++ gshow refineWrapper

-- things are a bit bad without type signatures. It's possible that
-- a polymorphic type has been inferred without it being intended. Then in
-- refine we should treat locally bound type variables as potentially
-- unifiable with concrete types

--    mapM (\n -> fmap (n,) (tcRnExprTc . noLoc . HsVar $ Exact n)) gblScope

  {-
  inHoleEnv stRef $ do
    mapM (_ . _) gblScope -- it wouldn't stick tcRnExprTc into that first hole 
-}
  {-
  inHoleEnv stRef
    n -}

