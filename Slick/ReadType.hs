{-# LANGUAGE LambdaCase #-}
module Slick.ReadType where

import           CoAxiom             (Role (Nominal))
import           Control.Monad.Error
import           DynFlags            (ExtensionFlag (Opt_PolyKinds))
import           ErrUtils            (Messages)
import           FamInst             (tcGetFamInstEnvs)
import           FamInstEnv          (normaliseType)
import           GHC                 (Type, runTcInteractive)
import           GhcMonad            (GhcMonad, getSession, getSessionDynFlags)
import           HsTypes             (LHsType, mkImplicitHsForAllTy)
import           Parser              (parseType)
import           RdrName             (RdrName)
import           RnEnv               (HsDocContext (GHCiCtx))
import           RnTypes             (rnLHsType)
import           SrcLoc              (noLoc)
import           TcHsType            (tcHsSigType)
import           TcRnMonad           (setXOptM)
import           TcType              (UserTypeCtxt (GhciCtxt))

import           Slick.Types
import           Slick.Util

-- useful things
-- RnTypes/rnHsTyKi
-- RnTypes/extractHsTysRdrTyVars
-- consider adding undbound type vars to environment

-- c/f TcRnDriver.hs/tcRnType. I just removed the failIfErrsM.
tcGetType
  :: GhcMonad m => LHsType RdrName -> m (Messages, Maybe Type)
tcGetType rdr_type = do
  hsc_env <- getSession
  _fs <- getSessionDynFlags -- is this call necessary at all? fs is never used
  liftIO . runTcInteractive hsc_env . setXOptM Opt_PolyKinds $ do
    (rn_type, _fvs) <- rnLHsType GHCiCtx (noLoc $ mkImplicitHsForAllTy (noLoc []) rdr_type)
    ty <- tcHsSigType GhciCtxt rn_type
    fam_envs <- tcGetFamInstEnvs
    let (_, ty') = normaliseType fam_envs Nominal ty
    return ty'

-- any kind quantifications should ideally be pushed in all the way.
-- for now I'm happy to replace

readType :: String -> M Type
readType str =
  lift (runParserM parseType str) >>= \case
    Left s  -> throwError $ ParseError s
    Right t -> do
      -- let errMsg = "Could not make sense of type in current env."
      (_, mt) <- lift (tcGetType t)
      maybe (throwError TypeNotInEnv) return mt

-- getTypeQuantified str =

