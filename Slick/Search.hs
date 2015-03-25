{-# LANGUAGE TupleSections, RecordWildCards #-}

module Slick.Search where

import Control.Applicative
import Slick.Types
import qualified Data.Map as M
import UniqSupply
import Control.Monad.State
import HsExpr
import Type
import Name
import Slick.Refine
import Slick.Suggest
import Slick.Util
import Slick.GhcUtil
import Data.IORef
import TcRnMonad hiding (mapMaybeM)

instance MonadUnique m => MonadUnique (StateT s m) where
  getUniqueSupplyM = lift getUniqueSupplyM

-- type Term = HsExpr RdrName

-- use Names for generated variables
type ProofState = M.Map Name (Int, Type)

inHoleEnv' :: IORef SlickState -> TcRn a -> M a
inHoleEnv' stRef tcx = do
  hi <- holeInfo <$> getCurrentHoleErr stRef
  tcmod <- typecheckedModule <$> getFileDataErr stRef
  inHoleEnv tcmod hi tcx

matches :: IORef SlickState -> Type -> ProofState -> M [(Name, RefineMatch)]
matches stRef goal = _ . clearOut where -- mapMaybeM (\(n, ty) -> fmap (fmap (n,)) . inHoleEnv' stRef $ refineMatch goal ty) . clearOut where
  clearOut = map (\(n, (_, ty)) -> (n, ty)) . filter ((> 0) . fst . snd) . M.toList

comm :: Maybe [a] -> [Maybe a]
comm x = maybe mzero (fmap pure)

-- fmap^n lets us touch the inner most letter without touching any others

-- Observations from looking at suggestions generated:
-- the actual correct term to refine with, mapMaybeM, is hopelessly far
-- down the list. However, refineMatch, which is contained in the final term we
-- want, is basically #3 on the list.
--
-- The search has to work by trying to get the target type of refineMatch,
-- TcRn (Maybe RefineMatch), to match the goal type M [(Name, RefineMatch)]
-- (And first it has to greedily introduce variables)

ps | refineMatch _ _                :: [(Name, Type)] | TcRn (Maybe RefineMatch)
-- work from the outside in, start on turning TcRn into M
ps | inHoleEnv' _ (refineMatch _ _) :: [(Name, Type)] | M (Maybe RefineMatch)
-- how do you know to use mapM? It has an argument where M (Maybe RefineMatch) occurs
-- positively and returns M [_], which is our current goal
ps | mapM (\x -> inHoleEnv' _ (refineMatch _ _)) _ :: [(Name, Type)] | M [Maybe RefineMatch]
-- Now the environment has changed, try to go fill in old holes. When faced
-- with ambiguity, use naming conventions to help you decide. E.g.,
-- refineMatch's first argument should be goal since that was the name of
-- the parameter in the definition.
ps | mapM (\x -> inHoleEnv' stRef (refineMatch goal (snd x))) _ :: [(Name, Type)] | M [Maybe RefineMatch]

-- better to hypothesize things that you can't immediately prove.
-- working inside out.
ps | fmap (fmap (_name,)) refineMatch _ _  :: [(Name, Type)] | TcRn (Maybe RefineMatch)
ps | fmap (fmap (_name,)) refineMatch _ _  :: [(Name, Type)] | TcRn (Maybe (Name, RefineMatch)) -- RefineMatch `turns into` (Name, RefineMatch)
ps | mapMaybeM (\x -> fmap (fmap (_name,)) refineMatch _ _) _  :: [(Name, Type)] | TcRn [(Name, RefineMatch)] -- Maybe `turns into` []

  -- or possibly
  ps | mapM (\x -> fmap (fmap (_name,)) refineMatch _ _) _  :: [(Name, Type)] | TcRn (List (Maybe (Name, RefineMatch))) -- we throw a list on the barby
  ps | fmap catMaybes (mapM (\x -> fmap (fmap (_name,)) refineMatch _ _) _)  :: [(Name, Type)] | TcRn (List (Maybe (Name, RefineMatch))) -- catMaybes lets us contract
  ps | fmap catMaybes (mapM (\x -> fmap (fmap (_name,)) refineMatch _ _) _)  :: [(Name, Type)] | TcRn (List (Name, RefineMatch)) -- catMaybes lets us contract maybe
  ps | inHoleEnv' _ (fmap catMaybes (mapM (\x -> fmap (fmap (_name,)) refineMatch _ _) _))  :: [(Name, Type)] | M (List (Name, RefineMatch)) -- catMaybes lets us contract maybe
  -- this is incorrect but still pretty good.
  -- Now we fill our debts
  ps | inHoleEnv' stRef (fmap catMaybes (mapM (\x -> fmap (fmap (_name,)) refineMatch _ _) _))  :: [(Name, Type)] | M (List (Name, RefineMatch)) -- catMaybes lets us contract maybe
  -- greedily deconstruct
  ps | inHoleEnv' stRef (fmap catMaybes (mapM (\(n,t) -> fmap (fmap (n,)) refineMatch t t) ps))  :: [(Name, Type)] | M (List (Name, RefineMatch)) -- catMaybes lets us contract maybe

ps | mapMaybeM (\x -> fmap (fmap (_name,)) refineMatch _ _) _  :: [(Name, Type)] | TcRn [(Name, RefineMatch)] -- Maybe `turns into` []


ps | (refineMatch _ _)  :: [(Name, Type)] | TcRn (Maybe RefineMatch)
ps | fmap (fmap (_name,)) (refineMatch _ _)  :: [(Name, Type)] | TcRn (Maybe (Name, RefineMatch))
ps | traverse (\x -> fmap (fmap (_name,)) (refineMatch _ _)) _ :: [(Name, Type)] | TcRn [Maybe (Name, RefineMatch)] -- justify this move
-- pull things you want to eliminate (like maybe) to the left.
-- "sequence" provides a commutation relation (albeit the wrong one in this
-- case. we should use the elimination relation catMaybes)
ps | fmap sequence (traverse (\x -> fmap (fmap (_name,)) (refineMatch _ _)) _) :: [(Name, Type)] | TcRn (Maybe [(Name, RefineMatch)])
-- use elimination relation on Maybe
ps | fmap (maybe _ id) $ fmap sequence (traverse (\x -> fmap (fmap (_name,)) (refineMatch _ _)) _) :: [(Name, Type)] | TcRn (Maybe [(Name, RefineMatch)])
-- I think we could use something like the levenstein algorithm in this
-- case since the size never increases

{-
_ :: [(Name, Type)] -> M [(Name, RefineMatch)]
-- first check if there's anything in scope that really takes [(_, _)].
-- otherwise, we try to "level" the source and the target types.
-- traverse can peel off a level
traverse _ :: (Name, Type) -> M (Name, RefineMatch)
-- cancel out name somehow
-}
{-
Want to construct
a -> F b
  find something of type
  f :: a' -> b
  can level to get
  fmap f :: F a' -> F b

  find something of type
  f :: a' -> F b
  can level to get
  (>>= f) :: F a' -> F b

  find something of type
  f :: a' -> G b
  k :: {G b, args*} -> F b
  can get
  k (f _) _ ... _ :: {a -> a', args*} -> F b

-}

search stRef goal pst = do
  ms <- matches stRef goal pst
  undefined

-- should be a forward kind of proof search
-- if search can't proceed, then case on some shit
-- kind of a focusing dealy

-- search takes hypotheses 

-- search :: Hypeotheses -> 
