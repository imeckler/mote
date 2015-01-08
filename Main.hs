{-# LANGUAGE PatternSynonyms, DeriveFunctor #-}
module Main where

import Language.Haskell.Exts.Syntax hiding (Pat(..))
import Control.Monad.Except
import Control.Monad.RWS
import Control.Applicative
import Data.Functor.Fixedpoint
import Data.Functor.Product
import Data.Functor.Constant

data Lit 
  = LInt Int
  | LString String
  | LList [Lit]
  deriving (Show)

data PatternF r
  = PCon String [r]
  | PConInfix String r r
  | PTuple [r]
  | PList [r]
  | PLit Lit
  | PVar String Type
  deriving (Show, Functor)

type Var = String

-- newtype NamedF = (,) (Maybe Var)

type NamedPatternF = (Product (Constant (Maybe Var)) PatternF)
type Pattern       = Fix NamedPatternF

pattern Named x p     = Fix (Pair (Constant (Just x)) p)
pattern Nameless p    = Fix (Pair (Constant Nothing) p)
pattern Pat p <- Fix (Pair _ p)

type Err = ExceptT String

data Env
type M = RWS Env () Int

-- Not exactly the right type...
findDecl :: QName -> M (Maybe Decl)
findDecl = undefined

pushAndPop sx = do
  s <- get
  x <- sx
  put s
  return x

data AppResult
  = AppVar Name -- f t
  | AppName QName Type -- F t
  | 

interp

tyApp :: Type -> Type -> M AppResult

typePatterns :: Type -> M [Pattern]
typePatterns t0 = pushAndPop $ case t0 of
  TyTuple Boxed ts -> do
    ps <- mapM (freshVar "x") ts
    return [Nameless (PTuple ps)]

  TyList t -> do
    x <- freshVar "x" t
    xs <- freshVar "xs" (TyList t)
    return [Nameless (PLit (LList [])), Nameless (PConInfix ":" x xs)]

  TyApp t1 t2 = undefined

  TyCon 

  TyVar _name -> freshVar "x" t0

  where
  freshVar :: String -> Type -> Counting Pattern
  freshVar s t = do
    i <- get
    put (i + 1)
    return $ Nameless (PVar (s ++ show i) t)

-- patterns 
