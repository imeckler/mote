{-# LANGUAGE LambdaCase #-}
module ReadType where

import GHC
import GhcMonad
import TcRnMonad(setXOptM)
import TcType (UserTypeCtxt(GhciCtxt))
import DynFlags(ExtensionFlag(Opt_PolyKinds))
import RnTypes (rnLHsType)
import RnEnv (HsDocContext(GHCiCtx), bindLocatedLocalsRn)
import CoAxiom(Role(Nominal))
import FamInst (tcGetFamInstEnvs)
import FamInstEnv (normaliseType)
import TcHsType (tcHsSigType)
import TcEnv (tcExtendTyVarEnv)
import Parser (parseType)
import UniqSet (uniqSetToList)
import Var (mkTyVar)
import Kind (anyKind)
import HsTypes
import Util

-- c/f TcRnDriver.hs/tcRnType. I just removed the failIfErrsM.
tcGetType rdr_type = do
  hsc_env <- getSession
  fs <- getSessionDynFlags
  liftIO . runTcInteractive hsc_env . setXOptM Opt_PolyKinds $ do
    (rn_type, _fvs) <- rnLHsType GHCiCtx (noLoc $ mkImplicitHsForAllTy (noLoc []) rdr_type)
    ty <- tcHsSigType GhciCtxt rn_type
    fam_envs <- tcGetFamInstEnvs
    let (_, ty') = normaliseType fam_envs Nominal ty
    return ty'

readType str =
  runParserM parseType str >>= \case
    Left _  -> return Nothing
    Right t -> fmap snd (tcGetType t)

-- getTypeQuantified str =

