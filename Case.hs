{-# LANGUAGE LambdaCase,
             RecordWildCards,
             NamedFieldPuns,
             TupleSections #-}
module Case where

import FastString(fsLit)
import RdrName (mkVarUnqual, nameRdrName)
import BasicTypes(Boxity(..))
import TyCon
import DataCon
import Control.Monad
import Util
import Type
import Control.Applicative
import GHC
import Bag (bagToList)
import TcRnMonad(setXOptM)
import DynFlags(ExtensionFlag(Opt_PolyKinds))
import FamInst (tcGetFamInstEnvs)
import qualified FamInstEnv
import CoAxiom(Role(Nominal))
import GhcMonad
import Data.Maybe
import HsPat
import UniqSupply
import Name (mkInternalName, mkVarOcc, nameOccName)
import Control.Arrow
import qualified Data.List as List
import Types
import Control.Monad.Error

type SatDataConRep = (Name, [Type])

type TypedDataCon = (DataCon, [Type])
type DataType = [TypedDataCon]

normaliseType :: (GhcMonad m) => Type -> m Type
normaliseType t = do
  hsc_env <- getSession
  fmap (fromMaybe t . snd) . liftIO . runTcInteractive hsc_env $
    setXOptM Opt_PolyKinds $ do
      fam_envs <- tcGetFamInstEnvs
      return (snd (FamInstEnv.normaliseType fam_envs Nominal t))

-- TODO: It's probably unnecessary to normalise here

unpeel :: GhcMonad m => Type -> m (Maybe DataType)
unpeel t =
  fmap (splitTyConApp_maybe . dropForAlls) (normaliseType t) >>| \case
    Nothing         -> Nothing
    Just (tc, args) -> 
      fmap (map (\dc -> (dc, dataConInstArgTys dc args)))
        (tyConDataCons_maybe tc)

-- algorithm for expanding variable.
-- > be in a hole.
-- > walk down parse tree looking for srcpos of that hole
-- > keep stack of case exprs you've stepped into.
-- > after finding the hole, walk back up and find the closest
--   one that has a variable named as requested.
-- > replace case exprs with expanded one
-- conPattern :: TypedDataCon -> UniqSM (Pat Name)
conPattern (dc, argTys)
  | isTupleDataCon dc =
    let b    = if isUnboxedTupleCon dc then Unboxed else Boxed 
        pats = zipWith varPat argTys [0..] 
    in
    TuplePat pats b argTys
  | otherwise = 
    ConPatIn (noLoc . nameRdrName $ dataConName dc) deets
  where
  deets
    | dataConIsInfix dc = case argTys of
        [x, y] -> InfixCon (varPat x 0) (varPat y 1)
    -- TODO: Records
    | otherwise = PrefixCon $ zipWith varPat argTys [0..]

varPat :: Type -> Int -> LPat RdrName
varPat t i = noLoc . VarPat . mkVarUnqual . fsLit $ "x" ++ show i

-- zipWithM f xs = sequence . zipWith f xs

-- noLoc
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
-- TODO: Refine with single constructor things


data MatchInfo id
  = Equation (Located id) -- name of the function in which this match is an equation
  | SingleLambda SrcSpan -- the srcspan of the whole lambda
  | CaseBranch

namesBound (L _ (Match pats t rhs)) = listyPat (\pats' -> Match pats' t rhs) pats where

  goPat = \case
    WildPat _        -> []
    VarPat x         -> [(x, id)]
    LazyPat p        -> wrapWith LazyPat (goLPat p)
    AsPat x p        -> wrapWith (AsPat x) (goLPat p)
    ParPat p         -> wrapWith ParPat (goLPat p)
    BangPat p        -> wrapWith BangPat (goLPat p)
    TuplePat ps b ts -> listyPat (\ps' -> TuplePat ps' b ts) ps
    ListPat ps t e   -> listyPat (\ps' -> ListPat ps' t e) ps
    PArrPat ps t     -> listyPat (\ps' -> PArrPat ps' t) ps
    ConPatIn c deets -> case deets of
      InfixCon a1 a2 -> listyPat (\[a1', a2'] -> ConPatIn c (InfixCon a1' a2')) [a1, a2]
      PrefixCon args -> listyPat (ConPatIn c . PrefixCon) args
      RecCon {}      -> error "TODO: Record field namesBound"

    ConPatOut {}     -> error "TODO: ConPatOut"
    ViewPat {}       -> error "TODO: ViewPat"
    SplicePat {}     -> error "TODO: SplicePat"
    QuasiQuotePat {} -> error "TODO: QuasiQuotePat"
    LitPat {}        -> []
    NPat {}          -> []
    NPlusKPat {}     -> error "TODO: NPlusKPat"
    SigPatIn lp bs   -> wrapWith (\lp' -> SigPatIn lp' bs) (goLPat lp)
    SigPatOut lp t   -> wrapWith (\lp' -> SigPatOut lp' t) (goLPat lp)
    CoPat co p t     -> wrapWith (\p' -> CoPat co p' t) (goPat p)

  wrapWith k = map (second (k.))

  listyPat :: ([LPat id] -> a) -> [LPat id] -> [(id, Pat id -> a)]
  listyPat k ps = concatMap (\(l, p, r) -> wrapWith (\p' -> k (l ++ p' : r)) (goLPat p)) (listViews ps)

  goLPat (L l p) = map (second (L l .)) (goPat p)

  listViews = go [] where
    go pre []     = []
    go pre (x:xs) = (pre, x, xs) : go (x:pre) xs


-- expansions :: (VarName, loc) -> Module -> Maybe ((MatchInfo, [Pat]), UniqSupply)
-- TODO: Change to ErrorT

expansions
  :: String
     -> Type
     -> SrcSpan
     -> HsModule RdrName
     -> M (Maybe
             ((LMatch RdrName (LHsExpr RdrName),
               MatchInfo RdrName),
              [Match RdrName (LHsExpr RdrName)]))
expansions var ty loc mod =
  case findMap (\mgi@(lm,_) -> fmap (mgi,) . aListLookup varName . namesBound $ lm) mgs of
    Just (mgi, patPosn) -> do
      dcsMay <- lift $ unpeel ty
      return $ case dcsMay of
        Nothing  -> Nothing
        Just dcs -> Just (mgi, map (patPosn . conPattern) dcs)

    Nothing -> throwError $ NoVariable var
  where
  varName       = mkVarUnqual $ fsLit var
  mgs           = containingMatchGroups loc mod
  findMap f     = foldr (\x r -> f x <|> r) Nothing
  aListLookup k = fmap snd . List.find ((== k) . fst)

-- matchToExpand loc var 

containingMatchGroups loc = goDecls [] . hsmodDecls where
  goDecls acc = goDecl acc . nextSubexpr loc

  goDecl acc = \case
    ValD bd                                   -> goBind acc bd
    InstD (ClsInstD (ClsInstDecl{cid_binds})) -> goBind acc . nextSubexpr loc $ bagToList cid_binds
    _                                         -> acc

  goBind acc = \case
    FunBind {..} -> goMatchGroup (Equation fun_id) acc $ fun_matches
    PatBind {..} -> goGRHSs acc pat_rhs
    _            -> acc

  goMatchGroup mi acc = maybe acc (goLMatch mi acc) . List.find ((loc `isSubspanOf`) . getLoc) . mg_alts

  goLMatch mi acc lm@(L _ (Match _pats _ty grhss)) = goGRHSs ((lm, mi):acc) grhss

  goGRHSs acc (GRHSs {grhssGRHSs}) = goGRHS acc $ nextSubexpr loc grhssGRHSs

  -- TODO: Guards should be returned too
  goGRHS acc (GRHS _gs b) = goLExpr acc b

  goLExpr acc (L l e) = case e of
    HsLamCase _ mg      -> goMatchGroup CaseBranch acc mg
    HsLam mg            -> goMatchGroup (SingleLambda l) acc mg
    HsApp a b           -> goLExpr acc $ nextSubLExpr [a, b]
    OpApp a b _ c       -> goLExpr acc $ nextSubLExpr [a, b, c]
    NegApp e' _         -> goLExpr acc e'
    HsPar e'            -> goLExpr acc e'
    SectionL a b        -> goLExpr acc $ nextSubLExpr [a, b]
    SectionR a b        -> goLExpr acc $ nextSubLExpr [a, b]
    ExplicitTuple ts _  -> goLExpr acc . nextSubLExpr $ mapMaybe (\case {Present e -> Just e; _ -> Nothing}) ts
    HsCase scrut mg     -> goMatchGroup CaseBranch acc mg
    HsIf _ a b c        -> goLExpr acc . nextSubLExpr $ [a, b, c]
    HsMultiIf _ grhss   -> goGRHS acc . nextSubexpr loc $ grhss
    HsDo _ stmts _      -> goStmt acc . nextSubexpr loc $ stmts
    ExplicitList _ _ es -> goLExpr acc . nextSubLExpr $ es
    ExplicitPArr _ es   -> goLExpr acc . nextSubLExpr $ es
    -- TODO: let expr
    _                   -> acc

  nextSubLExpr = fromMaybe (error "Where?") . List.find ((loc `isSubspanOf`) . getLoc)

  goStmt acc = \case
    LastStmt e _synE           -> goLExpr acc e -- TODO: figure out what the deal is with syntaxexpr
    BindStmt _lhs rhs _se _se' -> goLExpr acc rhs
    BodyStmt e _se _se' _      -> goLExpr acc e
    -- TODO
    -- LetStmt bs                 -> goLocalBinds acc bs
    _                          -> acc

