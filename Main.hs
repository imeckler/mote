{-# LANGUAGE PatternSynonyms, 
             DeriveFunctor,
             TupleSections,
             DeriveTraversable,
             LambdaCase,
             DeriveFoldable #-}
module Main where

import Util
import Language.Haskell.Exts.Syntax hiding (Pat(..), Decl(..))
import qualified Language.Haskell.Exts.Syntax as S
import Control.Monad.RWS
import Control.Applicative
import Data.Functor.Fixedpoint
import Data.Functor.Product
import Data.Functor.Constant

data Lit 
  = LInt Int
  | LString String
  | LChar Char
  deriving (Show)

data PatternF r
  = PCon String [r]
  | PConInfix String r r
  | PTuple [r]
  | PList [r]
  | PLit Lit
  -- Including the type here is the only reason I'm using this rather than
  -- the Pat type from Language.Haskell.Exts.Syntax
  | PVar Var Type
  -- Simplified record patterns for now
  | PRec String [(String, Type)]
  deriving (Show, Functor, Foldable, Traversable)

type Var = String

-- newtype NamedF = (,) (Maybe Var)

type NamedPatternF = (Product (Constant (Maybe Var)) PatternF)
type Pattern       = Fix NamedPatternF

pattern Named x p     = Fix (Pair (Constant (Just x)) p)
pattern Nameless p    = Fix (Pair (Constant Nothing) p)

{-
pattern Pat x p <- Fix (Pair (Constant x) p)
pattern Pat' p  <- Fix (Pair _ p)

-}
withName x (Pat' p) = Named x p

data Env
type M = RWS Env () Int

-- Not exactly the right type...

-- For now, does not support GADTs

data TyDecl
  = TypeDecl SrcLoc Name [TyVarBind] Type
  | DataDecl SrcLoc DataOrNew Name [TyVarBind] [ConDecl] -- TODO: Context argument, QualConDecl
  deriving (Show)

data Ty = TyType Type | DataType [ConDecl]

data TyCon = Abs TyVarBind [TyVarBind] Ty

-- newtype DataType = DataType [ConDecl]

getName :: TyVarBind -> Name
getName b = case b of { KindedVar n _ -> n; UnkindedVar n -> n }

tyDeclToTyCon :: TyDecl -> Maybe TyCon
tyDeclToTyCon td = undefined where
  go td = case td of
    TypeDecl _ _ [] t        -> ResType t
    DataDecl _ _ _ [] cs     -> ResDataType (DataType cs)
    TypeDecl s n (x:xs) t    -> TyAbs x (go (TypeDecl s n xs t))
    DataDecl s n d (x:xs) cs -> TyAbs x (go (DataDecl s n d xs cs))

conDeclPattern :: ConDecl -> Pattern
conDeclPattern c = case c of
  -- Eventually have var names guided by type/user
  ConDecl n ts         ->
    PCon (nameToString n) (zipWith (\i t -> Nameless (PVar ("x" ++ show i) t)) [1..] ts)
  InfixConDecl t1 n t2 ->
    PConInfix (nameToString n) (Nameless (Var "x1" t1)) (Nameless (Var "x2" t2))
  RecDecl n fs         ->
    PRec (nameToString n) (concatMap (\(ns, t) -> map (\f -> (nameToString f, t)) ns) fs)
  where nameToString = \case { Ident s -> s; Symbol s -> s }

findDecl :: QName -> M (Maybe TyDecl)
findDecl = undefined

findTyOrTyCon :: QName -> M (Either TyCon Ty)
findTyOrTyCon name = undefined

findTyCon :: QName -> M TyCon

-- This is really a bit fiddly
whnf :: Type -> M (TyCon + Ty)
whnf t = case t of
  TyApp t1 t2 ->
    whnf t1 >>= \case
      Left (Abs x [] s)     -> Right <$> whnf (subst (x, t2) s)
      Left (Abs x (y:ys) s) -> return $ Left (Abs y ys (subst (x, t2) s))
      Right _               -> return $ Right t

  TyCon n -> findTyOrTyCon n

  TyParen t1 -> whnf t1

  TyInfix t1 op t2 ->
    findTyCon op >>= \case
      Abs x [y] s       -> Right <$> whnf (subst (y, t2) $ subst (x, t1) s)
      Abs x (y:y':ys) s -> return $ Left (Abs y' ys (subst (y, t2) $ subst (x, t1) s))
      _                 -> throwError $ "Infix op " ++ getName op ++ " expects >= 2 arguments"

  _                -> return $ Right (Type t)

pushAndPop sx = do
  s <- get
  x <- sx
  put s
  return x

type AppResult = Type -> M [Pattern]

tyApp :: Type -> Type -> M (Either TypeFun [Pattern]) -- Either keepgoing done
tyApp f t = case f of

substType :: (Name, Type) -> Type -> Type
substType p@(x, s) t = case t of
  TyVar y          -> if x == y then s else t
  TyFun t1 t2      -> TyFun (substType p t1) (substType p t2)
  TyTuple b t1     -> TyTuple b (substType p t1)
  TyList t1        -> TyList (substType p t1)
  TyParArray t1    -> TyParArray (substType p t1)
  TyApp t1 t2      -> TyApp (substType p t1) (substType p t2)
  TyCon _          -> t
  TyParen t1       -> substType p t1
  TyInfix t1 op t2 -> TyInfix (substType p t1) op (substType p t2)
  TyKind t1 k      -> TyKind (substType p t1) k
  TyPromoted _     -> t
  TyEquals t1 t2   -> TyEquals (substType p t1) (substType p t2)
  TyBang bt t1     -> TyBang bt (substType p t1)
  -- TODO
  TySplice _ -> undefined

appTyDecl :: TyDecl -> Type -> TyDecl
appTyDecl td t = case td of
  TypeDecl s n (y:ys) t -> TypeDecl substType (y, t)

substTyDecl :: (Name, Type) -> TyDecl -> Either Type TyDecl
substTyDecl p@(x, s) d = case d of

normalizeApp :: Type -> Type -> M Type
normalizeApp t1 t2 = case t1 of
  TyApp s1 s2 ->
    normalizeApp s1 s2 >>= \case
      Neutral -> Neutral
      _ ->

  TyVar _f -> Neutral

  TyCon name ->
    findDecl name >>= \case
      Just (TypeDecl _ )

crossProduct :: [[a]] -> [[a]]
crossProduct = sequence

data ClientState

data ToClient
  = Insert T.Text
  | SetCursor (Int, Int)

data FromClientMessage
  = Load FilePath
  | CaseFurther Var 
  | CaseOn Var
  | NextHole

type FromClient = (FromClientMessage, Pos)

-- a user's context consists of all the names in scope and their types,
-- all the types in scope and their definitions,
-- a tree of the case expression they're currently editing,
-- their position in this tree (with a zipper perhaps).
-- we map back and forth between (line no, char no) and position in
-- the case tree

-- every message from the user includes their text position.

-- on every filewrite, reparse and rebuild context.
-- parsing is relative fast, so this should be fine.

-- Expand p to case on x
-- As patterns only appear when you case on a variable

-- I resolve to do the stupidest posisble thing until it
-- gets too slow

caseOn :: HsModule _ -> Var -> (Pos, String)
caseOn m x =

unfold :: Var -> Pattern -> M [Pattern]
unfold x pat@(Pat n p) = case p of
  PList ps  -> (map (Pat n . PList). crossProduct) <$> mapM (unfold x) ps
  PTuple ps -> (map (Pat n . PTuple). crossProduct) <$> mapM (unfold x) ps
  PCon c ps -> (map (Pat n . PCon c) . crossProduct) <$> mapM (unfold x) ps
  PConInfix s pa pb ->
    (\pas pbs -> (Pat n . PConInfix) <$> pas <*> pbs) <$> unfold x pa <*> unfold x pb
  PVar y t -> if x == y then map (withName x) <$> typePatterns t else return [pat]
  PLit _ -> return [pat]

-- Expects whnormalized argument
tyPatterns :: Ty -> [Pattern]
tyPatterns ty = case ty of
  Type t      -> typePatterns t
  DataType cs -> map conDeclPattern cs
  where
  typePatterns t = case t of
    TyApp _ _ -> [Nameless (TyVar "x" t)]
    TyCon _   -> [Nameless (TyVar "x" t)]
    TyTuple Boxed ts ->
      return . Nameless . PTuple
      $ zipWith (\i t -> Nameless (TyVar ("x" ++ show i) t)) [1..] ts
    TyList t' ->
      let { x = Nameless (TyVar "x" t'); xs = Nameless (TyVar "xs" t) }
      in [Nameless (PList []), Nameless (PConInfix ":" x xs)]

