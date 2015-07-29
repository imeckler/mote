{-# LANGUAGE LambdaCase, NamedFieldPuns, NoMonomorphismRestriction,
             RecordWildCards, TupleSections, CPP #-}
module Mote.Holes where

import qualified Bag
import           BasicTypes          (isTopLevel)
import           Control.Applicative
import           Control.Monad.Error hiding (liftIO)
import           Data.Maybe
import qualified Data.Set            as S
import           ErrUtils
import           GHC
import           GhcMonad
import qualified OccName
import           Outputable
import           Mote.Types
import           Mote.Util

import HscTypes (hsc_dflags, hsc_HPT)
import           TcMType             (zonkCt, zonkTcType)
import           TcRnDriver          (tcTopSrcDecls)
import           TcRnMonad           (TcM, captureConstraints)
import           TcRnTypes           (Ct (..), CtEvidence (..),
                                      Implication (..), TcIdBinder (..),
                                      TcLclEnv (..), WantedConstraints (..),
                                      ctEvPred, ctEvidence, ctLoc, ctLocEnv,
                                      ctLocSpan, isHoleCt)
import UniqFM
-- Be careful with guessTarget. It might grab a compiled version
-- of a module instead of interpreting

-- TODO: It's not only arg holes that matter. We need to put parens around
-- non atomic expressions being applied to other things as well
-- TODO: appartently this isn't recursing into record fields
findArgHoles :: HsModule RdrName -> S.Set SrcSpan
findArgHoles = S.fromList . goDecls . hsmodDecls where
  goDecls = concatMap (goDecl . unLoc)

  goDecl = \case
    ValD bd                                   -> goBind bd
    InstD (ClsInstD (ClsInstDecl{cid_binds})) -> concatMap (goBind . unLoc) $ Bag.bagToList cid_binds
    _                                         -> []

  goBind = \case
    FunBind {..} -> goMatchGroup fun_matches
    PatBind {..} -> goGRHSs pat_rhs
    _            -> []

  goMatchGroup = concatMap goLMatch . mg_alts

#if __GLASGOW_HASKELL__ < 710
  goLMatch (L _ (Match _pats _ty grhss)) = goGRHSs grhss
#else
  goLMatch (L _ (Match {m_grhss})) = goGRHSs m_grhss
#endif

  goGRHSs (GRHSs {grhssGRHSs}) = concatMap (goGRHS . unLoc) grhssGRHSs

  -- TODO: Guards should be returned too
  goGRHS (GRHS _gs b) = goLExpr b

  goArgLExpr e = case unLoc e of
    HsVar (Unqual o) -> case OccName.occNameString o of { '_':_ -> [getLoc e]; _ -> [] }
    EWildPat         -> [getLoc e]
    _                -> goLExpr e

  goLExpr :: LHsExpr RdrName -> [SrcSpan]
  goLExpr (L _l e) = case e of
    HsLamCase _ mg      -> goMatchGroup mg
    HsLam mg            -> goMatchGroup mg
    HsApp a b           -> goArgLExpr b ++ goLExpr a
    OpApp a b _ c       -> concatMap goLExpr [a, b, c]
    NegApp e' _         -> goLExpr e'
    HsPar e'            -> goLExpr e'
    SectionL a b        -> concatMap goLExpr [a, b]
    SectionR a b        -> concatMap goLExpr [a, b]
#if __GLASGOW_HASKELL__ < 710
    ExplicitTuple ts _boxity ->
      concatMap goLExpr $ mapMaybe (\case {Present e -> Just e; _ -> Nothing}) ts
#else
    ExplicitTuple largs _boxity ->
      concatMap goLExpr $ mapMaybe (\case {L _ (Present e) -> Just e; _ -> Nothing}) largs
#endif
    HsCase scrut mg     -> goLExpr scrut ++ goMatchGroup mg
    HsIf _ a b c        -> concatMap goLExpr [a, b, c]
    HsMultiIf _ grhss   -> concatMap (goGRHS . unLoc) grhss
    HsDo _ stmts _      -> concatMap (goStmt . unLoc) stmts
    ExplicitList _ _ es -> concatMap goLExpr es
    ExplicitPArr _ es   -> concatMap goLExpr es
    -- TODO: let expr
    -- TODO: Record exprs
    _                   -> []

  goStmt = \case
    LastStmt e _synE           -> goLExpr e -- TODO: figure out what the deal is with syntaxexpr
    BindStmt _lhs rhs _se _se' -> goLExpr rhs
    BodyStmt e _se _se' _      -> goLExpr e
    -- TODO
    -- LetStmt bs                 -> goLocalBinds acc bs
    _                          -> []

type GHCHole = (CtEvidence, OccName.OccName)

holeSpan :: HoleInfo -> SrcSpan
holeSpan = ctLocSpan . ctLoc . holeCt

holeType :: HoleInfo -> Type
holeType = ctEvPred . ctEvidence . holeCt

holeNameString :: HoleInfo -> String
holeNameString = occNameToString . cc_occ . holeCt

getRelevantBindings :: Ct -> TcM [(Id, Type)]
getRelevantBindings ct = go 100 (tcl_bndrs lcl_env)
  where
  lcl_env = ctLocEnv $ ctLoc ct

  go _      [] = return []
  go n_left (TcIdBndr id top_lvl : tc_bndrs)
    | isTopLevel top_lvl = go n_left tc_bndrs
    | n_left == 0        = return []
    | otherwise          = do
      ty <- zonkTcType (idType id)
      ((id, ty) :) <$> go (n_left - 1) tc_bndrs

-- When you do anything in TcM, set TcGblEnv from the ParsedModule
-- and TcLocalEnv from the Ct's. Make sure ScopedTypeVariables is on
getHoleInfos :: Ref MoteState -> TypecheckedModule -> M [HoleInfo]
getHoleInfos stRef tcmod = do
  let (_, mod_details) = tm_internals_ tcmod
  case tm_renamed_source tcmod of
    Nothing             -> return [] -- TODO: Error
    Just (grp, _, _, _) -> do
      hsc_env0 <- lift getSession
      FileData {typecheckedModule} <- getFileDataErr stRef
      let summary = pm_mod_summary (tm_parsed_module typecheckedModule)
          mod_name = moduleName $ ms_mod summary
          dflags  = ms_hspp_opts summary
          -- TODO: The reason the overlapping instances bug was occuring
          -- is that the instances from the current module were hanging around
          -- in the hsc_env (in hsc_HPT) from when the file was loaded. To
          -- remedy this I delete the module's entry, which I think is
          -- kosher.
          hsc_HPT0 = hsc_HPT hsc_env0
          -- TODO: The modified env is now causing a separate issue...
          -- Not sure what it is, switching back to using hsc_env0 for now.
          hsc_env =
            hsc_env0
            { hsc_dflags = dflags
            , hsc_HPT    = delFromUFM hsc_HPT0 mod_name
            }

      ((_warningmsgs, errmsgs), mayHoles) <- liftIO . runTcInteractive hsc_env0 $ do
        (_, wc) <- captureConstraints $ tcTopSrcDecls mod_details grp
        let cts = filter isHoleCt $ wcCts wc
        mapM (zonkCt >=> (\ct -> HoleInfo ct <$> getRelevantBindings ct)) cts

      fs <- lift getSessionDynFlags
      case mayHoles of
        Just holes -> return holes
        Nothing    -> throwError . GHCError . ("Mote.Holes.getHoleInfos: " ++) . showSDoc fs . vcat $ pprErrMsgBag errmsgs
  where
  wcCts (WC {wc_insol, wc_impl}) =
    Bag.bagToList wc_insol ++ Bag.foldrBag (\impl r -> wcCts (ic_wanted impl) ++ r) []  wc_impl
