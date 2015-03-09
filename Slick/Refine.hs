{-# LANGUAGE FlexibleContexts, LambdaCase, RecordWildCards #-}
module Slick.Refine where

import           Control.Applicative ((<$>))
import           Control.Monad.Error (ErrorT (..), MonadError, lift, throwError)
import           Control.Monad.Trans (MonadIO, MonadTrans)
import           Data.IORef          (IORef)
import qualified Data.Set            as S
import           GhcMonad
import           HsExpr              (HsExpr (..), LHsExpr)
import           OccName             (mkVarOcc)
import           RdrName             (RdrName (Unqual))
import           SrcLoc              (noLoc, unLoc)
import           TcType              (TcSigmaType)
import           Type                (dropForAlls, mkForAllTys, splitForAllTys,
                                      splitFunTy_maybe)
import           TypeRep             (Type)

import           Slick.GhcUtil
import           Slick.ReadType
import           Slick.Types
import           Slick.Util

refineExpr
  :: Num b => IORef SlickState -> TcType.TcSigmaType -> LHsExpr RdrName -> ErrorT ErrorType Ghc b
refineExpr stRef goalTy e = do
  ty <- hsExprType e
  refineType stRef goalTy ty

refineType
  :: (MonadError ErrorType (t m), MonadTrans t, GhcMonad m,
      MonadIO (t m), Num b) =>
     IORef SlickState -> TcSigmaType -> TypeRep.Type -> t m b
refineType stRef goalTy t = let (tyVars, t') = splitForAllTys t in go 0 tyVars t'
-- foralls of the argument type t should get pushed down as we go
  where
  -- The subtype thing doesn't play nice with polymorphism.
  -- If we have a hole _ :: a (not forall a. a, it's a specific type
  -- variable) and refine with fromJust :: forall t. Maybe t -> t,
  -- subType says that a < the type of fromJust and we just stick fromJust
  -- in the hole.
  go acc tyVars t =
    let (tyVars', t') = splitForAllTys t
        tyVars'' = tyVars ++ tyVars'
    in
    do
      tyStr <- lift (showPprM (goalTy, mkForAllTys tyVars'' t))
      logS stRef $ "refineType: " ++ tyStr
      -- TODO: check what subtype does on (dropForAlls <$> readType "a") and
      -- (dropForAlls <$> readType "a")
      lift (subType goalTy (mkForAllTys tyVars'' t)) >>= \case
        True  -> return acc
        False -> case splitFunTy_maybe t' of
          Nothing      -> throwError NoRefine
          Just (_, t'') -> go (1 + acc) tyVars'' t''

refine :: IORef SlickState -> String -> M (LHsExpr RdrName)
refine stRef eStr = do
  h             <- getCurrentHoleErr stRef
  isArg         <- S.member h . argHoles <$> gReadIORef stRef
  HoleInfo {..} <- getCurrentHoleInfoErr stRef
  -- got rid of dropForAlls here, but that's definitely wrong as per const
  -- example
  --
  -- first order approximation: just instantiate all abstracted
  -- kindvars to *. I believe this is approximately correct since
  -- if there were real constraints on the kinds (ignoring prescribed type
  -- signature), they would have been put in the result of readType
  --
  -- this is complicated...
  goalTy        <- dropForAlls <$> readType holeTypeStr
  ErrorT . withBindings holeEnv . runErrorT $ do
    expr' <- refineToExpr stRef goalTy =<< parseExpr eStr
    let atomic =
          case unLoc expr' of
            HsVar {}     -> True
            HsIPVar {}   -> True
            HsOverLit {} -> True
            HsLit {}     -> True
            HsPar {}     -> True
            _            -> False
    return $ if isArg && not atomic then noLoc (HsPar expr') else expr'

refineToExpr
  :: IORef SlickState
     -> TcSigmaType
     -> LHsExpr RdrName
     -> ErrorT ErrorType Ghc (LHsExpr RdrName)
refineToExpr stRef goalTy e =
  refineExpr stRef goalTy e >>| \argsNum -> withNHoles argsNum e

withNHoles :: Int -> LHsExpr RdrName -> LHsExpr RdrName
withNHoles n e = app e $ replicate n hole where
  app f args = foldl (\f' x -> noLoc $ HsApp f' x) f args
  hole       = noLoc $ HsVar (Unqual (mkVarOcc "_"))

