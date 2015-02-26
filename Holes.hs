{-# LANGUAGE LambdaCase, 
             RecordWildCards,
             NamedFieldPuns,
             TupleSections,
             NoMonomorphismRestriction #-}
module Holes where

import Control.Applicative
import Data.Maybe
import Util
import GHC
import GhcMonad
import GHC.Paths
import Outputable
import qualified Data.Map as M
import Control.Monad.Error hiding (liftIO)
import Control.Monad.State hiding (liftIO)
import System.FilePath
import qualified DynFlags
import qualified OccName
import qualified Bag
import qualified Data.Set as S

-- TODO: In the future, I think it should be possible to actually get the
-- CHoleCan datastructure via runTcInteractive. Call getConstraintVar to
-- find the bag of constraints. CHoleCan's will be among them.
-- Getting "relevant bindings" seems to be a bit harder and it ends up
-- forcing ugly things like GetType (i.e., parsing types from strings)
-- since I can't get at the Type's any other way. Check relevantBindings
-- in TcErrors.hs to see how to get at the environment

type M = ErrorT String Ghc

-- Be careful with guessTarget. It might grab a compiled version
-- of a module instead of interpreting

argHoles = S.fromList . goDecls . hsmodDecls where
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

  goLMatch lm@(L _ (Match _pats _ty grhss)) = goGRHSs grhss

  goGRHSs (GRHSs {grhssGRHSs}) = concatMap (goGRHS . unLoc) grhssGRHSs

  -- TODO: Guards should be returned too
  goGRHS (GRHS _gs b) = goLExpr b

  goArgLExpr e = case unLoc e of
    HsVar (Unqual o) -> case OccName.occNameString o of { '_':_ -> [getLoc e]; _ -> [] }
    EWildPat         -> [getLoc e]
    _                -> goLExpr e

  goLExpr :: LHsExpr RdrName -> [SrcSpan]
  goLExpr (L l e) = case e of
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

{-
-- Holes which are arguments to functions and so might need parens
argHoles = S.fromList . goDecls . hsmodDecls where
  goDecls = concatMap (goDecl . unLoc)

  goDecl = \case
    ValD b                                    -> goBind b
    InstD (ClsInstD (ClsInstDecl{cid_binds})) -> concatMap (goBind . unLoc) $ Bag.bagToList cid_binds
    _                                         -> []

  goBind = \case
    FunBind {fun_matches} -> goMatchGroup fun_matches
    _                     -> []

  goMatchGroup (MG {mg_alts}) = concatMap (goMatch . unLoc) mg_alts

  goMatch (Match _ _ grhss) = goGRHSs grhss

  goGRHSs (GRHSs {grhssGRHSs}) = concatMap (goGRHS . unLoc) grhssGRHSs

  goGRHS (GRHS gs b) = goLExpr False b ++ concatMap (goStmt . unLoc) gs

  -- isArg is a flag indicating that the hole
  -- is an argument to a function and so might need parens upon being
  -- replaced
  goLExpr isArg (L l e) = case e of
    HsVar (Unqual o)    -> case OccName.occNameString o of { '_':_ -> if isArg then [l] else []; _ -> [] }
    HsLam mg            -> goMatchGroup mg
    HsLamCase _ mg      -> goMatchGroup mg
    HsApp a b           -> goLExpr False a ++ goLExpr True b
    OpApp a b _ c       -> goLExpr False a ++ goLExpr False b ++ goLExpr False c
    NegApp e' _         -> goLExpr False e'
    HsPar e'            -> goLExpr False e'
    SectionL a b        -> goLExpr False a ++ goLExpr False b
    SectionR a b        -> goLExpr False a ++ goLExpr False b
    ExplicitTuple ts _  -> concatMap (\case { Present e' -> goLExpr False e'; _ -> [] }) ts
    HsCase scrut mg     -> goLExpr False scrut ++ goMatchGroup mg
    HsIf _ a b c        -> goLExpr False a ++ goLExpr False b ++ goLExpr False c
    HsMultiIf _ grhss   -> concatMap (goGRHS . unLoc) grhss
    HsDo _ stmts _      -> concatMap (goStmt . unLoc) stmts
    ExplicitList _ _ es -> concatMap (goLExpr False) es
    ExplicitPArr _ es   -> concatMap (goLExpr False) es
    _                   -> []

  goStmt = \case
    LastStmt e _synE           -> goLExpr False e -- TODO: figure out what the deal is with syntaxexpr
    BindStmt _lhs rhs _se _se' -> goLExpr False rhs
    BodyStmt e _se _se' _      -> goLExpr False e
    LetStmt bs                 -> goLocalBinds bs
    _                          -> []

  goLocalBinds = \case
    HsValBinds vals -> goValBinds vals
    HsIPBinds ips   -> goIPBinds ips

  goValBinds = \case
    ValBindsIn bs _  -> goBinds bs
    ValBindsOut ps _ -> concatMap (goBinds . snd) ps

  goIPBinds _ = [] -- TODO: Figure out what this is

  goBinds = Bag.foldrBag (\b r -> goBind (unLoc b) ++ r) []
-}
runM :: M a -> IO (Either String a)
runM = runGhc (Just libdir) . runErrorT

setupImports = undefined

printScope = liftIO . putStrLn =<< showSDocM . ppr =<< getNamesInScope

localNames = getNamesInScope

-- when we step under a binder, record the binding and it's 
-- purported type from a signature. Always in our map we must
-- have 
--
-- TODO maintain a stack of "arg types". we pop off an arg and
-- assign it to a variable when we find one, recording this
-- in out writing
setupContext
  :: (OutputableBndr id, Ord id) =>
     SrcSpan
     -> HsModule id
     -> M ()
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

  goMatchGroup :: (OutputableBndr id) => MatchGroup id (LHsExpr id) -> StateT [HsType id] M ()
  goMatchGroup (MG {..}) =
    foldr (\(L l m) r -> if hole `isSubspanOf` l then goMatch m else r)
      (error "Where the hole?") mg_alts

  goStmt = \case
    LastStmt e _synE           -> error "goStmt:todo"
    BindStmt _lhs rhs _se _se' -> error "goStmt:todo"
    BodyStmt e _se _se' _      -> error "goStmt:todo"
    LetStmt bs                 -> error "goStmt:todo"
    _                          -> error "goStmt:todo"

 
  goGRHS (GRHS gs (L _ rhs)) = maybe (goExpr rhs) goStmt (nextSubexpr' hole gs)

  goGRHSs :: OutputableBndr id => GRHSs id (LHsExpr id) -> StateT [HsType id] M ()
  goGRHSs grhss = goGRHS $ nextSubexpr hole (grhssGRHSs grhss)
    -- TODO: use grhssLocalBinds ("the where clause")

  goMatch :: (OutputableBndr id) => Match id (LHsExpr id) -> StateT [HsType id] M ()
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
        let Match [L l pat] _ grhss = nextSubexpr hole mg_alts
        lift . lift $ do
          scrutStr <- showSDocM (ppr scrut)
          patStr   <- showSDocM (ppr pat)
          setBinding patStr scrutStr
        goGRHSs grhss

    HsLet bs e        -> error "todo: let"
    HsDo {}           -> error "todo: do"
    OpApp l op _fix r -> goExpr $ nextSubexpr hole [l, op, r]
    SectionL o x      -> goExpr $ nextSubexpr hole [o, x]
    SectionR o x      -> goExpr $ nextSubexpr hole [o, x]
    HsMultiIf _ grhss -> error "multiif"
    RecordUpd {}      -> error "todo: RecordUpd"

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

