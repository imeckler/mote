{-# LANGUAGE LambdaCase, NamedFieldPuns, NoMonomorphismRestriction,
             RecordWildCards, TupleSections #-}
module Slick.Holes where

import DynFlags
import qualified Bag
import           Control.Applicative
import ErrUtils
import           Control.Monad.Error hiding (liftIO)
import           Control.Monad.State hiding (liftIO)
import qualified Data.Map            as M
import           Data.Maybe
import HscTypes (HsParsedModule(..), HscEnv(..))
import qualified Data.Set            as S
import           GHC
import           GHC.Paths
import           GhcMonad
import qualified OccName
import           Outputable
import qualified PrelNames
import TcRnDriver (tcTopSrcDecls)
import BasicTypes (isTopLevel)
import           TcRnMonad           (getConstraintVar, readTcRef, TcM, captureConstraints)
import           TcRnTypes           (Ct (..), TcIdBinder(..), Implication(..), WantedConstraints (..), CtEvidence(..), TcLclEnv(..), isHoleCt, ctEvPred, ctEvidence, ctLoc, ctLocEnv, ctLocSpan)
import TcMType (zonkCt, zonkTcType)
import Inst (tyVarsOfCt)
import TcType (tyVarsOfType)
import VarSet (disjointVarSet)
import Slick.Types

import           Slick.Util

-- Be careful with guessTarget. It might grab a compiled version
-- of a module instead of interpreting

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

  goLMatch (L _ (Match _pats _ty grhss)) = goGRHSs grhss

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
    ExplicitTuple ts _  -> concatMap goLExpr $ mapMaybe (\case {Present e -> Just e; _ -> Nothing}) ts
    HsCase scrut mg     -> goLExpr scrut ++ goMatchGroup mg
    HsIf _ a b c        -> concatMap goLExpr [a, b, c]
    HsMultiIf _ grhss   -> concatMap (goGRHS . unLoc) grhss
    HsDo _ stmts _      -> concatMap (goStmt . unLoc) stmts
    ExplicitList _ _ es -> concatMap goLExpr es
    ExplicitPArr _ es   -> concatMap goLExpr es
    -- TODO: let expr
    _                   -> []

  goStmt = \case
    LastStmt e _synE           -> goLExpr e -- TODO: figure out what the deal is with syntaxexpr
    BindStmt _lhs rhs _se _se' -> goLExpr rhs
    BodyStmt e _se _se' _      -> goLExpr e
    -- TODO
    -- LetStmt bs                 -> goLocalBinds acc bs
    _                          -> []

-- when we step under a binder, record the binding and it's
-- purported type from a signature. Always in our map we must
-- have
--
-- TODO maintain a stack of "arg types". we pop off an arg and
-- assign it to a variable when we find one, recording this
-- in out writing
type MS = ErrorT String Ghc
setupContext
  :: (OutputableBndr id, Ord id) =>
     SrcSpan
     -> HsModule id
     -> MS ()
setupContext hole mod = goDecls decls where
  decls = hsmodDecls mod

  collectSigs =
    foldl (\m d -> case d of
      L _ (SigD (TypeSig lnames (L _ t))) ->
        let args = argTys t in
        foldl (\m' (L _ name) -> M.insert name args m') m lnames
      _                                       -> m)
      M.empty

  sigs = collectSigs decls

  goDecls = goDecl . nextSubexpr hole

  goDecl (ValD b) = goBind b
  goDecl _        = throwError "Hole not in a value expression"

  -- really should be doing normalization here
  argTys :: HsType name -> [HsType name]
  argTys = \case
    HsForAllTy _ _ _ t -> argTys (unLoc t)
    HsFunTy s t        -> unLoc s : argTys (unLoc t)
    _                  -> []

  goBind b = case b of
    FunBind {..} ->
      let tys     = fromMaybe [] $ M.lookup (unLoc fun_id) sigs
      in
      evalStateT (goMatchGroup fun_matches) tys
    PatBind {}    -> error "Expected FunBind but got PatBind"
    VarBind {}    -> error "Expected FunBind but got VarBind"
    AbsBinds {}   -> error "Expected FunBind but got AbsBinds"
    PatSynBind {} -> error "Expected FunBind but got PatSynBind"

  goMatchGroup :: (OutputableBndr id) => MatchGroup id (LHsExpr id) -> StateT [HsType id] MS ()
  goMatchGroup (MG {..}) =
    foldr (\(L l m) r -> if hole `isSubspanOf` l then goMatch m else r)
      (error "Where the hole?") mg_alts

  goStmt = \case
    LastStmt _e _synE           -> error "goStmt:todo"
    BindStmt _lhs _rhs _se _se' -> error "goStmt:todo"
    BodyStmt _e _se _se' _      -> error "goStmt:todo"
    LetStmt _bs                 -> error "goStmt:todo"
    _                           -> error "goStmt:todo"


  goGRHS (GRHS gs (L _ rhs)) = maybe (goExpr rhs) goStmt (nextSubexpr' hole gs)

  goGRHSs :: OutputableBndr id => GRHSs id (LHsExpr id) -> StateT [HsType id] MS ()
  goGRHSs grhss = goGRHS $ nextSubexpr hole (grhssGRHSs grhss)
    -- TODO: use grhssLocalBinds ("the where clause")

  goMatch :: (OutputableBndr id) => Match id (LHsExpr id) -> StateT [HsType id] MS ()
  goMatch (Match pats _ grhss) = do
    tys <- get
    (typedPats, untypedPats) <- case zipSplit pats tys of
      (typedPats, Right tys')       -> (typedPats, []) <$ put tys'
      (typedPats, Left untypedPats) -> (typedPats, untypedPats) <$ put []

    forM typedPats $ \(p, t) -> lift . lift $ do
      patStr <- showSDocM (ppr p)
      tyStr  <- showSDocM (ppr t)
      setBinding patStr ("undefined" ++ " :: " ++ tyStr)

    forM untypedPats $ \p -> lift . lift $ do
      patStr <- showSDocM (ppr p)
      setBinding patStr "undefined"

    goGRHSs grhss

  goExpr = \case
    HsLam mg              -> goMatchGroup mg
    HsLamCase _ty mg      -> goMatchGroup mg
    HsCase (L l scrut) (MG{..}) ->
      if hole `isSubspanOf` l
      then goExpr scrut
      else do
        let Match [L _l pat] _ grhss = nextSubexpr hole mg_alts
        lift . lift $ do
          scrutStr <- showSDocM (ppr scrut)
          patStr   <- showSDocM (ppr pat)
          setBinding patStr scrutStr
        goGRHSs grhss

    HsLet _bs _e       -> error "todo: let"
    HsDo {}            -> error "todo: do"
    OpApp l op _fix r  -> goExpr $ nextSubexpr hole [l, op, r]
    SectionL o x       -> goExpr $ nextSubexpr hole [o, x]
    SectionR o x       -> goExpr $ nextSubexpr hole [o, x]
    HsMultiIf _ _grhss -> error "multiif"
    RecordUpd {}       -> error "todo: RecordUpd"

    HsApp e1 e2         -> goExpr $ nextSubexpr hole [e1, e2]
    NegApp (L _ e) _    -> goExpr e
    HsPar (L _ e)       -> goExpr e
    ExplicitTuple ts _  -> goExpr . nextSubexpr hole $ mapMaybe (\case {Present e -> Just e; _ -> Nothing}) ts
    HsIf _ i t e        -> goExpr $ nextSubexpr hole [i, t, e]
    ExplicitList _ _ es -> goExpr $ nextSubexpr hole es
    ExplicitPArr _ es   -> goExpr $ nextSubexpr hole es
    RecordCon _ _ bs    -> goRecordBinds bs

    _ -> return ()

  goRecordBinds = undefined

  setBinding lhs rhs = runStmt ("let " ++ lhs ++ " = " ++ rhs) RunToCompletion

-- linearity ftw
zipSplit :: [a] -> [b] -> ([(a,b)], Either [a] [b])
zipSplit []     ys     = ([], Right ys)
zipSplit xs     []     = ([], Left xs)
zipSplit (x:xs) (y:ys) = let (ps, r) = zipSplit xs ys in ((x,y) : ps, r)

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
  ct_tvs  = tyVarsOfCt ct

  go _      [] = return []
  go n_left (TcIdBndr id top_lvl : tc_bndrs)
    | isTopLevel top_lvl = go n_left tc_bndrs
    | n_left == 0        = return []
    | otherwise          = do
      ty <- zonkTcType (idType id)
      ((id, ty) :) <$> go (n_left - 1) tc_bndrs

-- When you do anything in TcM, set TcGblEnv from the ParsedModule
-- and TcLocalEnv from the Ct's. Make sure ScopedTypeVariables is on
getHoleInfos :: TypecheckedModule -> M [HoleInfo]
getHoleInfos tcmod = ErrorT $ do
  let (_, mod_details) = tm_internals_ tcmod
  case tm_renamed_source tcmod of
    Nothing             -> return (Right []) -- TODO: Error
    Just (grp, _, _, _) -> do
      hsc_env <- getSession
      ((_warningmsgs, errmsgs), mayHoles) <- liftIO . runTcInteractive hsc_env $ do
        (_, wc) <- captureConstraints $ tcTopSrcDecls mod_details grp
        let cts = filter isHoleCt $ wcCts wc
        mapM (zonkCt >=> (\ct -> HoleInfo ct <$> getRelevantBindings ct)) cts

      fs <- getSessionDynFlags
      return $ case mayHoles of
        Just holes -> Right holes
        Nothing    -> Left . GHCError . showSDoc fs . vcat $ pprErrMsgBag errmsgs
  where
  wcCts (WC {wc_insol, wc_impl}) =
    Bag.bagToList wc_insol ++ Bag.foldrBag (\impl r -> wcCts (ic_wanted impl) ++ r) []  wc_impl
