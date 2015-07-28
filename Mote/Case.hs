{-# LANGUAGE LambdaCase, NamedFieldPuns, RecordWildCards, TupleSections,
             CPP #-}
module Mote.Case where

import           Bag                 (bagToList)
import           BasicTypes          (Boxity (..))
import           Control.Applicative ((<$), (<$>), (<*>), (<|>))
import           Control.Arrow       (second)
import           Control.Monad.Error (throwError)
import           Control.Monad.State
import qualified Data.List           as List
import           Data.Maybe          (fromMaybe, mapMaybe)
import qualified Data.Set            as S
import qualified Data.Char as Char
import qualified Data.IntervalMap.FingerTree as I
import           DataCon             (DataCon, dataConFieldLabels,
                                      dataConInstArgTys, dataConIsInfix,
                                      dataConName, isTupleDataCon,
                                      dataConUserType,
                                      isUnboxedTupleCon)
import           DynFlags            (ExtensionFlag (Opt_PolyKinds))
import           FamInst             (tcGetFamInstEnvs)
import qualified FamInstEnv
import           FastString
import qualified GHC
import           GhcMonad
import           HsBinds             (HsBindLR (..), HsLocalBindsLR (..),
                                      HsValBindsLR (..))
import           HsDecls             (ClsInstDecl (..), HsDecl (..),
                                      InstDecl (..))
import           HsExpr              (GRHS (..), GRHSs (..), HsExpr (..),
                                      HsTupArg (..), LHsExpr, LMatch,
                                      Match (..), StmtLR (..))
import           HsPat
import           HsSyn               (HsModule (..))
import           Name                (Name)
import           OccName             (occNameString, occNameFS, occName)
import           RdrName             (RdrName (..), mkVarUnqual, nameRdrName)
import           SrcLoc              (GenLocated (..), Located, SrcLoc(..), SrcSpan,
                                      getLoc, isSubspanOf, noLoc, realSrcSpanStart)
import           TcRnDriver          (runTcInteractive)
import           TcRnMonad           (setXOptM)
import           TyCon
import           Type
import           TypeRep
#if __GLASGOW_HASKELL__ >= 710
import Var (mkGlobalVar)
import IdInfo(IdDetails(VanillaId), vanillaIdInfo)
#endif

import           Mote.Types
import           Mote.Util

type SatDataConRep = (Name, [Type])

type TypedDataCon = (DataCon, [Type])
type DataType = [TypedDataCon]

type NAME = RdrName

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

type Scoped = State (S.Set FastString)


-- algorithm for expanding variable.
-- > be in a hole.
-- > walk down parse tree looking for srcpos of that hole
-- > keep stack of case exprs you've stepped into.
-- > after finding the hole, walk back up and find the closest
--   one that has a variable named as requested.
-- > replace case exprs with expanded one

conPattern :: S.Set FastString -> (DataCon, [Type]) -> Pat NAME
conPattern scope (dc, argTys)
  | isTupleDataCon dc =
    let b    = if isUnboxedTupleCon dc then Unboxed else Boxed
        pats = evalState (mapM varPat argTys) scope
    in
    TuplePat pats b []
  | otherwise =
      ConPatIn (noLoc (nameRdrName (dataConName dc)))
      {-
        (noLoc
          (mkGlobalVar VanillaId (dataConName dc) (dataConUserType dc) vanillaIdInfo)) -}
        deets
      {- (noLoc (nameRdrName (dataConName dc))) -}
    -- ConPatIn (noLoc . nameRdrName $ dataConName dc) deets
  where
  deets :: HsConPatDetails NAME
  deets
    | dataConIsInfix dc = case argTys of
        [x, y] -> evalState (InfixCon <$> varPat x <*> varPat y) scope
        _      -> error "Unexpected number of arguments to an infix constructor."
    -- TODO: Records
    | otherwise = 
      case dataConFieldLabels dc of
        [] -> PrefixCon (evalState (mapM varPat argTys) scope)
        fs -> RecCon $
          HsRecFields
          { rec_flds   =
#if __GLASGOW_HASKELL__ < 710
              map (\l -> HsRecField (noLoc (Exact l)) (noLoc $ WildPat undefined) pun) fs
#else
              map (\x ->
                noLoc $
                  HsRecField {  hsRecFieldId = noLoc (nameRdrName x), hsRecFieldArg = (noLoc $ WildPat undefined), hsRecPun = pun })
                fs
#endif
          , rec_dotdot = Nothing
          }
          where
          -- TODO: Only pun if the extension is on
          pun = True

varPat :: Type -> Scoped (LPat NAME)
varPat t = noLoc . VarPat . mkVarUnqual <$> freshWithPrefix (typePrefix t)

freshWithPrefix :: FastString -> Scoped FastString
freshWithPrefix pre = do
  s <- get 
  if not (pre `S.member` s)
    then pre <$ modify (S.insert pre)
    else freshWithPrefix (appendFS pre (fsLit "'"))

-- Should be a normalized type as argument, though not with
-- synonyms expanded
typePrefix :: Type -> FastString
typePrefix = fsLit . typePrefix' where
  typePrefix' = \case
    AppTy {}         -> "x"
    -- TODO: This will probably break on infix tycons
    -- TODO: Special case maybe
    -- TODO: Special case either
    -- TODO: Type variables
    TyConApp tc args ->
      if isListTyCon tc
      then typePrefix' (head args) ++ "s"
      else if isTupleTyCon tc
      then List.intercalate "_and_" (map typePrefix' args)
      else initials $ occNameString (occName (tyConName tc))

    FunTy s t     -> concat [typePrefix' s, "_to_", typePrefix' t]
    ForAllTy _x t -> typePrefix' t
    LitTy t       -> case t of
      StrTyLit fs -> unpackFS fs
      NumTyLit n  -> '_' : show n
    TyVarTy _v    -> "x"

    where
    initials :: String -> [Char]
    initials (c : cs) = Char.toLower c : initials (dropWhile Char.isLower cs)
    initials []       = []

isListTyCon :: TyCon -> Bool
isListTyCon tc = occNameString (occName (tyConName tc)) == "[]"
-- TODO: This version not working for some reason
-- isListTyCon tc = tc `hasKey` consDataConKey


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

namesBound
  :: GenLocated t (Match id body) -> [(id, Pat id -> Match id body)]
#if __GLASGOW_HASKELL__ < 710
namesBound (L _ (Match m_pats m_type m_grhss)) =
  listyPat (\m_pats' -> Match m_pats' m_type m_grhss) m_pats
#else
namesBound (L _ m@(Match {m_pats, m_type, m_grhss})) =
  listyPat (\m_pats' -> m { m_pats = m_pats' }) m_pats
#endif
  where
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
      RecCon (HsRecFields {rec_flds, rec_dotdot}) -> case rec_dotdot of
        Just _  -> [] -- TODO: This should really expand out the dotdot
        Nothing ->
#if __GLASGOW_HASKELL__ < 710
          concatMap (\(pre,fld,post) ->
            wrapWith (wrap pre fld post) . goLPat $ hsRecFieldArg fld)
            (listViews rec_flds)
          where
          wrap pre fld post lp =
            ConPatIn c $
              RecCon (HsRecFields (pre ++ fld { hsRecFieldArg = lp } : post) Nothing)
#else
          concatMap (\(pre,lfld,post) ->
            wrapWith (wrap pre lfld post) . goLPat . hsRecFieldArg $ GHC.unLoc lfld)
            (listViews rec_flds)
          where
          wrap pre lfld post p' =
            ConPatIn c
              (RecCon
                (HsRecFields
                  (pre ++ fmap (\fld -> fld { hsRecFieldArg = p' }) lfld : post)
                  Nothing))
#endif

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
    go _ []       = []
    go pre (x:xs) = (pre, x, xs) : go (x:pre) xs


patternsForType :: S.Set FastString -> Type -> M [LPat RdrName]
patternsForType scope ty =
  lift (unpeel ty) >>| \case
    Just dt -> map (noLoc . conPattern scope) dt
    Nothing -> [evalState (varPat ty) scope]

scopeAt :: Ref MoteState -> SrcLoc -> M (S.Set FastString)
scopeAt stRef loc = do
  FileData {scopeMap} <- getFileDataErr stRef
  return $ S.fromList . map (occNameFS . occName . snd) . I.search loc $ scopeMap

matchesForTypeAt :: Ref MoteState -> Type -> SrcLoc -> M [Match RdrName (LHsExpr RdrName)]
matchesForTypeAt stRef ty loc = do
  scope <- scopeAt stRef loc
#if __GLASGOW_HASKELL__ < 710
  fmap (map (\p -> Match [p] Nothing holyGRHSs))
#else
  fmap (map (\p -> Match { m_fun_id_infix = Nothing, m_pats = [p], m_type = Nothing, m_grhss = holyGRHSs }))
#endif
    (patternsForType scope ty)
  where
  holyGRHSs :: GRHSs RdrName (LHsExpr RdrName)
  holyGRHSs = GRHSs [noLoc $ GRHS [] (noLoc EWildPat)] EmptyLocalBinds

-- TODO: We have an actual Var at our disposal now when we call this so the
-- string argument can be replaced with a Var argument
expansions
  :: Ref MoteState
     -> String
     -> Type
     -> SrcSpan
     -> HsModule RdrName
     -> M (Maybe
             ((LMatch RdrName (LHsExpr RdrName),
               MatchInfo RdrName),
              [Match RdrName (LHsExpr RdrName)]))
expansions stRef var ty loc mod =
  case findMap (\mgi@(lm,_) -> fmap (mgi,) . aListLookup varName . namesBound $ lm) mgs of
    Just (mgi, patPosn) -> do
      dcsMay <- lift $ unpeel ty
      scope  <- scopeAt stRef (RealSrcLoc $ realSrcSpanStart (toRealSrcSpan loc))
      case dcsMay of
        Nothing  -> return Nothing
        Just dcs -> do
          let matches = map (patPosn . conPattern scope) dcs
          logS stRef . show $
            map (\(dc, args) -> (dataConIsInfix dc, map typePrefix args)) dcs -- lift (showSDocM . vcat . map (pprMatch (CaseAlt :: HsMatchContext RdrName)) $ matches)
          return $ Just (mgi, matches)

    Nothing -> throwError $ NoVariable var
  where
  varName       = mkVarUnqual $ fsLit var
  mgs           = containingMatchGroups loc mod
  findMap f     = foldr (\x r -> f x <|> r) Nothing
  aListLookup k = fmap snd . List.find ((== k) . fst)

-- matchToExpand loc var

containingMatchGroups :: SrcSpan -> HsModule id ->
                         [(GenLocated SrcSpan (Match id (GenLocated SrcSpan (HsExpr id))), MatchInfo id)]
containingMatchGroups loc = goDecls [] . GHC.hsmodDecls where
  goDecls acc = goDecl acc . nextSubexpr loc

  goDecl acc = \case
    ValD bd                                            -> goBind acc bd
    InstD (ClsInstD (ClsInstDecl {cid_binds})) ->
      goBind acc . nextSubexpr loc $ bagToList cid_binds
    _                                                      -> acc

  goBind acc = \case
    FunBind {..} -> goMatchGroup (Equation fun_id) acc $ fun_matches
    PatBind {..} -> goGRHSs acc pat_rhs
    _            -> acc

  goMatchGroup mi acc =
    maybe acc (goLMatch mi acc) . List.find ((loc `isSubspanOf`) . getLoc) . GHC.mg_alts

  goLMatch mi acc
#if __GLASGOW_HASKELL__ < 710
    lm@(L _ (Match _pats _ty m_grhss)) =
#else
    lm@(L _ (Match {m_grhss})) =
#endif
      goGRHSs ((lm, mi):acc) m_grhss

  goGRHSs acc (GRHSs { grhssGRHSs, grhssLocalBinds }) =
    case nextSubexpr' loc grhssGRHSs of
      Just g -> goGRHS acc g
      Nothing -> goLocalBinds acc grhssLocalBinds

  goLocalBinds acc = \case
    HsValBinds vb -> goValBinds acc vb
    HsIPBinds {} -> acc
    EmptyLocalBinds -> acc

  goValBinds acc vbs = goBind acc . nextSubexpr loc $ case vbs of
    ValBindsIn bs _sigs   -> bagToList bs
    ValBindsOut rbs _sigs -> concatMap (bagToList . snd) rbs


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
    ExplicitTuple args _boxity  ->
#if __GLASGOW_HASKELL__ < 710
      goLExpr acc . nextSubLExpr $
        mapMaybe (\case {Present e -> Just e; _ -> Nothing}) args
#else
      goLExpr acc . nextSubLExpr $
        mapMaybe (\case {L _ (Present e) -> Just e; _ -> Nothing}) args
#endif
    HsCase _scrut mg    -> goMatchGroup CaseBranch acc mg
    HsIf _ a b c        -> goLExpr acc . nextSubLExpr $ [a, b, c]
    HsMultiIf _ grhss   -> goGRHS acc . nextSubexpr loc $ grhss
    HsDo _ stmts _      -> goStmt acc . nextSubexpr loc $ stmts
    ExplicitList _ _ es -> goLExpr acc . nextSubLExpr $ es
    ExplicitPArr _ es   -> goLExpr acc . nextSubLExpr $ es
    -- TODO: let expr
    _                   -> acc

  nextSubLExpr =
    let find = List.find :: (a -> Bool) -> [a] -> Maybe a in
    fromMaybe (error "Where?") . find ((loc `isSubspanOf`) . getLoc)

  goStmt acc = \case
    LastStmt e _synE           -> goLExpr acc e -- TODO: figure out what the deal is with syntaxexpr
    BindStmt _lhs rhs _se _se' -> goLExpr acc rhs
    BodyStmt e _se _se' _      -> goLExpr acc e
    -- TODO
    -- LetStmt bs                 -> goLocalBinds acc bs
    _                          -> acc

