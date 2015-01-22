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

type M = ErrorT String Ghc

-- Be careful with guessTarget. It might grab a compiled version
-- of a module instead of interpreting

holes = goDecls . hsmodDecls where
  goDecls = concatMap (goDecl . unLoc)

  goDecl = \case
    ValD b -> goBind b
    _      -> []

  goBind = \case
    FunBind {fun_matches} -> goMatchGroup fun_matches
    _                     -> []

  goMatchGroup (MG {mg_alts}) = concatMap (goMatch . unLoc) mg_alts

  goMatch (Match _ _ grhss) = goGRHSs grhss

  goGRHSs (GRHSs {grhssGRHSs}) = concatMap (goGRHS . unLoc) grhssGRHSs

  goGRHS (GRHS gs b) = goLExpr b ++ concatMap (goStmt . unLoc) gs

  goLExpr (L l e) = case e of
    HsVar (Unqual o)    -> case OccName.occNameString o of { '_':_ -> [l] ; _ -> [] }
    HsLam mg            -> goMatchGroup mg
    HsLamCase _ mg      -> goMatchGroup mg
    HsApp a b           -> goLExpr a ++ goLExpr b
    OpApp a b _ c       -> goLExpr a ++ goLExpr b ++ goLExpr c
    NegApp e' _         -> goLExpr e'
    HsPar e'            -> goLExpr e'
    SectionL a b        -> goLExpr a ++ goLExpr b
    SectionR a b        -> goLExpr a ++ goLExpr b
    ExplicitTuple ts _  -> concatMap (\case { Present e' -> goLExpr e'; _ -> [] }) ts
    HsCase scrut mg     -> goLExpr scrut ++ goMatchGroup mg
    HsIf _ a b c        -> goLExpr a ++ goLExpr b ++ goLExpr c
    HsMultiIf _ grhss   -> concatMap (goGRHS . unLoc) grhss
    HsDo _ stmts _      -> concatMap (goStmt . unLoc) stmts
    ExplicitList _ _ es -> concatMap goLExpr es
    ExplicitPArr _ es   -> concatMap goLExpr es
    _                   -> error "goLExpr: todo"

  goStmt = \case
    LastStmt e _synE           -> goLExpr e -- TODO: figure out what the deal is with syntaxexpr
    BindStmt _lhs rhs _se _se' -> goLExpr rhs
    BodyStmt e _se _se' _      -> goLExpr e
    LetStmt bs                 -> goLocalBinds bs
    _                          -> error "goStmt: todo"

  goLocalBinds = \case
    HsValBinds vals -> goValBinds vals
    HsIPBinds ips   -> goIPBinds ips

  goValBinds = \case
    ValBindsIn bs _  -> goBinds bs
    ValBindsOut ps _ -> concatMap (goBinds . snd) ps

  goIPBinds _ = [] -- TODO: Figure out what this is

  goBinds = Bag.foldrBag (\b r -> goBind (unLoc b) ++ r) []

runM :: M a -> IO (Either String a)
runM = runGhc (Just libdir) . runErrorT

setupImports = undefined

output = liftIO . putStrLn <=< showSDocM . ppr

printScope = liftIO . putStrLn =<< showSDocM . ppr =<< getNamesInScope

localNames = getNamesInScope

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

  goDecls = goDecl . nextSubexpr

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

  goGRHSs :: OutputableBndr id => GRHSs id (LHsExpr id) -> StateT [HsType id] M ()
  goGRHSs grhss = 
    foldr (\(L _ (GRHS gs (L l rhs))) r -> if hole `isSubspanOf` l then goExpr rhs else r)
      (error "Where the hole?") (grhssGRHSs grhss)
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

  nextSubexpr = foldr (\(L l x) r -> if hole `isSubspanOf` l then x else r) (error "where")

  goExpr = \case
    HsLam mg              -> goMatchGroup mg
    HsLamCase _ty mg      -> goMatchGroup mg
    HsCase (L l scrut) (MG{..}) -> 
      if hole `isSubspanOf` l
      then goExpr scrut
      else do
        let Match [L l pat] _ grhss = nextSubexpr mg_alts
        lift . lift $ do
          scrutStr <- showSDocM (ppr scrut)
          patStr   <- showSDocM (ppr pat)
          setBinding patStr scrutStr
        goGRHSs grhss

    HsLet bs e        -> error "todo: let"
    HsDo {}           -> error "todo: do"
    OpApp {}          -> error "lookup arg order OpApp"
    SectionL {}       -> error "lookup arg order SectionL"
    SectionR {}       -> error "lookup arg order SectionR"
    HsMultiIf _ grhss -> error "multiif"
    RecordUpd {} -> error "todo: RecordUpd"

    HsApp e1 e2         -> goExpr $ nextSubexpr [e1, e2]
    NegApp (L _ e) _    -> goExpr e
    HsPar (L _ e)       -> goExpr e
    ExplicitTuple ts _  -> goExpr . nextSubexpr $ mapMaybe (\case {Present e -> Just e; _ -> Nothing}) ts
    HsIf _ i t e        -> goExpr $ nextSubexpr [i, t, e]
    ExplicitList _ _ es -> goExpr $ nextSubexpr es
    ExplicitPArr _ es   -> goExpr $ nextSubexpr es
    RecordCon _ _ bs    -> goRecordBinds bs
    
    _ -> return ()
  
  goRecordBinds = undefined

  setBinding lhs rhs = runStmt ("let " ++ lhs ++ " = " ++ rhs) RunToCompletion

-- linearity ftw
zipSplit :: [a] -> [b] -> ([(a,b)], Either [a] [b])
zipSplit []     ys     = ([], Right ys)
zipSplit xs     []     = ([], Left xs)
zipSplit (x:xs) (y:ys) = let (ps, r) = zipSplit xs ys in ((x,y) : ps, r)

