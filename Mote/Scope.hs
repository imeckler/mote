{-# LANGUAGE LambdaCase, NamedFieldPuns, RecordWildCards, CPP #-}
module Mote.Scope where

import           Bag
import qualified Data.IntervalMap.FingerTree as I
import           Data.Maybe                  (mapMaybe)
import           FastString                  (nilFS)
import           GHC
import           RdrName                     (mkVarUnqual)
import           Mote.Types
import           SrcLoc
import Mote.Util

type Accum a = ScopeMap -> a -> ScopeMap

-- TODO: Might be able to do this same thing for TypecheckedModule and get
-- at the real Names
makeScopeMap :: HsModule RdrName -> ScopeMap
makeScopeMap = goDecls I.empty . hsmodDecls where
  goDecls :: ScopeMap -> [LHsDecl RdrName] -> ScopeMap
  goDecls acc = foldl (\m d -> goDecl m d) acc

  goDecl :: Accum (LHsDecl RdrName)
  goDecl acc (L _ d) = case d of
    InstD id  -> goInstDecl acc id
    ValD b    -> goBind acc b
    _         -> acc

  goInstDecl :: Accum (InstDecl RdrName)
  goInstDecl acc id = case id of
    DataFamInstD _              -> acc
    TyFamInstD _                -> acc
    ClsInstD (ClsInstDecl {..}) -> goLBinds acc cid_binds

  goLBinds :: Accum (LHsBinds RdrName)
  goLBinds acc bs = foldlBag (\m b -> goBind m (unLoc b)) acc bs

  -- TODO: top level bindings should be everywhere
  -- TODO: Find out what bind_fvs is 
  goBind :: Accum (HsBind RdrName)
  goBind acc = \case
    FunBind {fun_matches}      -> goMatchGroup acc fun_matches
    PatBind {pat_lhs, pat_rhs} ->
      let acc' = foldl (\m id -> I.insert scopeSpan id m) acc (lpatNamesBound pat_lhs) in
      goGRHSs acc' pat_rhs
      where
      scopeSpan = foldl1 lub (map (toSrcLocInterval . getLoc) (grhssGRHSs pat_rhs))
    _ -> acc

  -- TODO: Where clause? I guess that's with the GRHSs in localBinds
  goMatchGroup :: Accum (MatchGroup RdrName (LHsExpr RdrName))
  goMatchGroup = \acc (MG {mg_alts}) -> foldl goLMatch acc mg_alts
    where
    goLMatch :: Accum (LMatch RdrName (LHsExpr RdrName))
    goLMatch acc (L lm (Match ps _ty grhss)) =
      let acc' = insertManyAt (toSrcLocInterval lm) (concatMap lpatNamesBound ps) acc
      in goGRHSs acc' grhss

  -- TODO: grhssLocalBinds
  goGRHSs :: Accum (GRHSs RdrName (LHsExpr RdrName))
  goGRHSs acc (GRHSs {grhssGRHSs, grhssLocalBinds = _}) = foldl (\m g -> goGRHS m (unLoc g)) acc grhssGRHSs

  -- TODO: Guard 
  goGRHS :: Accum (GRHS RdrName (LHsExpr RdrName))
  goGRHS acc (GRHS _guardStmt lexpr) = goLExpr acc lexpr

  goLocalBinds :: Accum (HsLocalBinds RdrName)
  goLocalBinds acc lb = case lb of
    HsIPBinds (IPBinds ips _evbinds)   -> goMany (\m (L _ (IPBind _ lexpr)) -> goLExpr m lexpr) acc ips
    EmptyLocalBinds                    -> acc
    HsValBinds (ValBindsOut rbs _sigs) -> goMany goLBinds acc (map snd rbs)
    HsValBinds (ValBindsIn bs _sigs)   -> goLBinds acc bs

  goLExpr :: Accum (LHsExpr RdrName)
  goLExpr acc (L l e) = case e of
    HsLam mg                -> goMatchGroup acc mg
    HsLamCase _ty mg        -> goMatchGroup acc mg
    HsApp e1 e2             -> goMany goLExpr acc [e1, e2]
    OpApp e1 e2 _fix e3     -> goMany goLExpr acc [e1, e2, e3]
    NegApp e _se            -> goLExpr acc e
    HsPar e                 -> goLExpr acc e
    SectionL e1 e2          -> goMany goLExpr acc [e1, e2]
    SectionR e1 e2          -> goMany goLExpr acc [e1, e2]
    ExplicitTuple args _box -> goMany goLExpr acc (mapMaybe (\case {Present e -> Just e; _ -> Nothing}) args)
    HsCase scrut mg         -> goMatchGroup (goLExpr acc scrut) mg
    HsIf _se e1 e2 e3       -> goMany goLExpr acc [e1, e2, e3]
    HsMultiIf _ty grhss     -> goMany (\m g -> goGRHS m (unLoc g)) acc grhss -- goMany (\acc g -> goGRHSs acc (unLoc g)) acc grhss
    HsLet lbs e             ->
      let acc' = foldl (\m rn -> I.insert (toSrcLocInterval l) rn m) acc (localBindsNamesBound lbs) in
      goLExpr (goLocalBinds acc' lbs) e
    HsDo _ctx stmts _ty      ->
      let end = RealSrcLoc $ realSrcSpanEnd (toRealSrcSpan l) 
          upd :: Accum (ExprLStmt RdrName, ExprLStmt RdrName)
          upd m (L ls s, L ls' _) = case s of
            BindStmt p _e _se _se' -> 
              let scope = I.Interval (RealSrcLoc . realSrcSpanStart $ toRealSrcSpan ls') end in
              insertManyAt scope (lpatNamesBound p) m

            LetStmt locbinds ->
              let scope = I.Interval (RealSrcLoc . realSrcSpanStart $ toRealSrcSpan ls) end in
              insertManyAt scope (localBindsNamesBound locbinds) m

            _ -> m -- TODO

          acc' = foldl upd acc (zip stmts (tail stmts))
      in
      goMany (\m s -> goStmt m (unLoc s)) acc' stmts

    ExplicitList _ty _se es         -> goMany goLExpr acc es
    ExplicitPArr _ty es             -> goMany goLExpr acc es
    RecordCon _recName _ty recBinds -> goRecordBinds acc recBinds
    RecordUpd e bs _cons _tys _tys' -> goRecordBinds (goLExpr acc e) bs
    ExprWithTySig e _ty             -> goLExpr acc e
    ExprWithTySigOut e _ty          -> goLExpr acc e
    ArithSeq _ty _se seqInfo        -> goArithSeqInfo acc seqInfo
    PArrSeq _ty seqInfo             -> goArithSeqInfo acc seqInfo
    HsSCC _fs e                     -> goLExpr acc e
    HsCoreAnn _fs e                 -> goLExpr acc e
    -- Begin template haskell stuff
    HsBracket {}      -> acc
    HsRnBracketOut {} -> acc
    HsTcBracketOut {} -> acc
    HsSpliceE {}      -> acc
    HsQuasiQuoteE {}  -> acc
    -- End template haskell stuff
    HsProc {}          -> acc -- TODO
    HsTick _tick e     -> goLExpr acc e
    HsBinTick _t _t' e -> goLExpr acc e
    HsTickPragma _t e  -> goLExpr acc e
    HsWrap _w e        -> goLExpr acc (L l e)
    _                  -> acc

  goRecordBinds :: Accum (HsRecordBinds RdrName)
  goRecordBinds acc (HsRecFields {rec_flds, rec_dotdot=_}) = goMany goRecField acc rec_flds
    where
    goRecField :: Accum (HsRecField RdrName (LHsExpr RdrName))
    goRecField m (HsRecField {hsRecFieldArg}) = goLExpr m hsRecFieldArg

  goArithSeqInfo :: Accum (ArithSeqInfo RdrName)
  goArithSeqInfo acc x = case x of
    FromThen e1 e2      -> goMany goLExpr acc [e1, e2]
    FromTo e1 e2        -> goMany goLExpr acc [e1, e2]
    FromThenTo e1 e2 e3 -> goMany goLExpr acc [e1, e2, e3]
    From e1             -> goLExpr acc e1

  goStmt :: Accum (Stmt RdrName (LHsExpr RdrName))
  goStmt acc s = case s of
    BindStmt _p e _se _se'         -> goLExpr acc e
    BodyStmt e _se _se' _ty        -> goLExpr acc e
    LetStmt lbs                    -> goLocalBinds acc lbs
    ParStmt parStmtBlocks _se _se' -> goMany goParStmtBlock acc parStmtBlocks
    LastStmt e _se                 -> goLExpr acc e
    -- TODO
    TransStmt {} -> acc
    RecStmt {}   -> acc

  goParStmtBlock :: Accum (ParStmtBlock RdrName RdrName)
  goParStmtBlock acc (ParStmtBlock stmts _rns _se) = goMany (\m -> goStmt m . unLoc) acc stmts

  goMany :: Accum a -> Accum [a]
  goMany = foldl

  insertManyAt :: I.Interval SrcLoc -> [RdrName] -> ScopeMap -> ScopeMap
  insertManyAt i rns m = foldl (\m rn -> I.insert i rn m) m rns

  toSrcLocInterval :: SrcSpan -> I.Interval SrcLoc
  toSrcLocInterval = \case
    UnhelpfulSpan _ -> I.Interval unhelpful unhelpful
      where unhelpful = UnhelpfulLoc nilFS
    RealSrcSpan sp -> I.Interval (RealSrcLoc $ realSrcSpanStart sp) (RealSrcLoc $ realSrcSpanEnd sp)

  lub :: Ord v => I.Interval v -> I.Interval v -> I.Interval v
  lub (I.Interval {I.low=l1, I.high=h1}) (I.Interval {I.low=l2, I.high=h2}) =
    I.Interval {I.low=min l1 l2, I.high=max h1 h2}

lpatNamesBound :: LPat id -> [id]
lpatNamesBound = patNamesBound . unLoc

localBindsNamesBound :: HsLocalBinds RdrName -> [RdrName]
localBindsNamesBound loc = case loc of
  HsIPBinds (IPBinds ipBinds _evbinds) -> map (extract . unLoc) ipBinds
  EmptyLocalBinds                      -> []
  HsValBinds vbs                       -> case vbs of
    ValBindsOut rbs _sigs -> concatMap (lhsBindsNamesBound . snd) rbs
    ValBindsIn bs _sigs   -> lhsBindsNamesBound bs
  where
  extract :: IPBind RdrName -> RdrName
  extract (IPBind name _) = case name of
    Right id           -> id
    Left (HsIPName fs) -> mkVarUnqual fs

lhsBindsNamesBound :: LHsBindsLR RdrName RdrName -> [RdrName]
lhsBindsNamesBound bs = foldBag (++) (hsBindNamesBound . unLoc) [] bs

hsBindNamesBound :: HsBind RdrName -> [RdrName]
hsBindNamesBound b = case b of
  FunBind {fun_id}     -> [unLoc fun_id]
  PatBind {pat_lhs}    -> lpatNamesBound pat_lhs
  VarBind {var_id}     -> [var_id]
  AbsBinds {abs_binds} -> lhsBindsNamesBound abs_binds
#if __GLASGOW_HASKELL__ < 710
  PatSynBind {patsyn_args} ->
#else
  PatSynBind (PSB {psb_args=patsyn_args}) ->
#endif
    case patsyn_args of
      PrefixPatSyn lrs  -> map unLoc lrs
      InfixPatSyn r1 r2 -> [unLoc r1, unLoc r2]

patNamesBound :: Pat id -> [id]
patNamesBound = \case
  VarPat id                           -> [id]
  LazyPat p                           -> lpatNamesBound p
  AsPat lid p                         -> unLoc lid : lpatNamesBound p
  ParPat p                            -> lpatNamesBound p
  BangPat p                           -> lpatNamesBound p
  ListPat ps _ty _                    -> concatMap lpatNamesBound ps
  TuplePat ps _boxity _ty             -> concatMap lpatNamesBound ps
  PArrPat ps _ty                      -> concatMap lpatNamesBound ps
  ConPatIn _ deets                    -> detailsNamesBound deets
  ConPatOut {pat_args}                -> detailsNamesBound pat_args
  ViewPat _expr p _ty                 -> lpatNamesBound p
  SplicePat (HsSplice id _)           -> [id] -- TODO: I don't actually know what I'm doing here
  QuasiQuotePat (HsQuasiQuote id _ _) -> [id] -- TODO: Or here
  LitPat _                            -> []
  NPat _ _ _                          -> [] -- TODO
  NPlusKPat (L _ id) _ _ _            -> [id]
  SigPatIn p _                        -> lpatNamesBound p -- TODO: HsWithBndrs
  SigPatOut p _ty                     -> lpatNamesBound p
  CoPat _wrapper p _ty                -> patNamesBound p
  WildPat _ty                         -> []
  where
  detailsNamesBound :: HsConPatDetails id -> [id]
  detailsNamesBound = \case
    RecCon (HsRecFields {rec_flds, rec_dotdot}) -> case rec_dotdot of
      _ -> concatMap hsRecFieldNamesBound rec_flds -- TODO: do something different in the dotdot case?
    InfixCon p1 p2                              -> lpatNamesBound p1 ++ lpatNamesBound p2
    PrefixCon ps                                -> concatMap lpatNamesBound ps

  hsRecFieldNamesBound :: HsRecField id (LPat id) -> [id]
  hsRecFieldNamesBound (HsRecField {hsRecFieldId, hsRecFieldArg, hsRecPun}) = case hsRecPun of
    True  -> [unLoc hsRecFieldId]
    False -> lpatNamesBound hsRecFieldArg

