{-# LANGUAGE LambdaCase #-}
module Case where

import TyCon
import DataCon
import Util
import Type
import Control.Applicative
import GHC
import TcRnMonad(setXOptM)
import DynFlags(ExtensionFlag(Opt_PolyKinds))
import FamInst (tcGetFamInstEnvs)
import qualified FamInstEnv
import CoAxiom(Role(Nominal))
import GhcMonad
import Data.Maybe
import HsPat

type SatDataConRep = (Name, [Type])

type TypedDataCon = (DataCon, [Type])
type DataType = [SatDataConRep]


normaliseType :: (GhcMonad m) => Type -> m Type
normaliseType t = do
  hsc_env <- getSession
  fmap (fromMaybe t . snd) . liftIO . runTcInteractive hsc_env $
    setXOptM Opt_PolyKinds $ do
      fam_envs <- tcGetFamInstEnvs
      return (snd (FamInstEnv.normaliseType fam_envs Nominal t))

unpeel :: GhcMonad m => Type -> m (Maybe DataType)
unpeel t =
  fmap splitTyConApp_maybe (normaliseType t) >>| \case
    Nothing         -> Nothing
    Just (tc, args) -> 
      fmap (map (\dc -> (dataConName dc, dataConInstArgTys dc args)))
        (tyConDataCons_maybe tc)

dummyLocated :: a -> Located a
dummyLocated = L (error "dummyLocated")

newName :: m Name
newName = undefined

{-
patterns :: Type -> m [Pat id]
patterns t =
  t' <- normaliseType t
  unpeel t' >>= \case
    Nothing -> [SigPatOut (dummyLocated $ VarPat )]
-}
-- cases :: HsType -> Ty
