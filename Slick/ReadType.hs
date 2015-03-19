{-# LANGUAGE LambdaCase #-}
module ReadType where

import           CoAxiom             (Role (Nominal))
import           Control.Monad.Error
import           DynFlags            (ExtensionFlag (Opt_PolyKinds))
import           FamInst             (tcGetFamInstEnvs)
import           FamInstEnv          (normaliseType)
import           GHC                 (Type, runTcInteractive)
import           GhcMonad            (GhcMonad, getSession, getSessionDynFlags)
import           HsTypes             (LHsType, mkImplicitHsForAllTy)
import           Kind                (anyKind)
import           Name                (Name)
import           Parser              (parseType)
import           RnEnv               (HsDocContext (GHCiCtx),
                                      bindLocatedLocalsRn)
import           RnTypes             (rnLHsType)
import           SrcLoc              (noLoc)
import           TcEnv               (tcExtendTyVarEnv)
import           TcHsType            (tcHsSigType)
import           TcRnMonad           (setXOptM)
import           TcType              (UserTypeCtxt (GhciCtxt))
import           UniqSet             (uniqSetToList)
import           Var                 (mkTyVar)

import           Slick.GhcUtil       (withTyVarsInScope)
import           Slick.Types
import           Slick.Util

-- useful things
-- RnTypes/rnHsTyKi
-- RnTypes/extractHsTysRdrTyVars
-- consider adding undbound type vars to environment

-- c/f TcRnDriver.hs/tcRnType. I just removed the failIfErrsM.
rdrTypeToTypeWithTyVarsInScope tvNames rdr_type = do
  hsc_env <- getSession
  liftIO
    . runTcInteractive hsc_env
    . setXOptM Opt_PolyKinds
    . withTyVarsInScope tvNames
    $ tcRdrTypeToType rdr_type

tcRdrTypeToType rdr_type = do
  (rn_type, _fvs) <- rnLHsType GHCiCtx (noLoc $ mkImplicitHsForAllTy (noLoc []) rdr_type)
  ty <- tcHsSigType GhciCtxt rn_type
  fam_envs <- tcGetFamInstEnvs
  let (_, ty') = normaliseType fam_envs Nominal ty
  return ty'

-- any kind quantifications should ideally be pushed in all the way.
-- for now I'm happy to replace

readTypeWithTyVarsInScope :: [Name] -> String -> M Type
readTypeWithTyVarsInScope tvNames str =
  lift (runParserM parseType str) >>= \case
    Left s  -> throwError $ ParseError s
    Right t -> do
      let errMsg = "Could not make sense of type in current env."
      (_, mt) <- lift (rdrTypeToTypeWithTyVarsInScope tvNames t)
      maybe (throwError TypeNotInEnv) return mt

readType :: String -> M Type
readType = readTypeWithTyVarsInScope []

-- getTypeQuantified str =

