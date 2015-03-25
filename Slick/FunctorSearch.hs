{-# LANGUAGE DeriveGeneric, StandaloneDeriving #-}
module Slick.FunctorSearch where

import HsExpr
import Data.Maybe
import RdrName
import Data.IORef
import TypeRep
import Slick.Util
import qualified Data.Map as M

type ProofTerm   = HsExpr RdrName

type FunctorName = Type
type Expr        = [FunctorName]
type Sequent     = (Expr, Expr)

-- curr goal -> new goals,  goals proof term -> curr proof term
-- type Rule' = Rule Ide
type Rule ms mp s p = (s -> ms (Maybe [s]), [p] -> mp p)
type RuleChooser ms mp s p = s -> ms [ ([s], [p] -> mp p) ]

identityFunction = undefined

-- In the future, maybe we have a better way of finding applicable rules
-- than testing all of them.
search :: (Functor m, Monad m) => RuleChooser m m s p -> s -> m [p]
search chooseRules seq = do
  nexts <- chooseRules seq
  fmap concat $ mapM (\(seqs, build) ->
    mapM build . cartProd =<< mapM (search chooseRules) seqs) nexts
  where cartProd = sequence

searchMemo chooseRules abort = \seq -> do
  memo <- newIORef M.empty
  where
  maxDepth = 10
  memoed memo x k = (readIORef memo >>| M.lookup x) >>= maybe k return

  go d memo seq = 
    M.lookup seq <$> readIORef memo >>= \case
      Nothing     -> -- never been tried before
      Just proofs -> do
        let cheapProofs = 
        mapMaybe (\(cost, proof) -> whenMay (cost <= maxDepth - d) proof) proofs
        
        forM proofs $ \(cost, proof) ->
          if cost > maxDepth - d

    nexts <- chooseRules seq
    forM nexts $ \(goals, build) -> do
      forM goals $ \
      go memo 

    nexts <- chooseRules seq
    forM nexts $ 

  whenMay b x = if b then Just x else Nothing

-- search :: 

{-
-- data ProofTree = ProofTree Sequent Rule [ProofTree]
search :: Int -> Sequent -> [ProofTerm]
search n seq =
  concat
  . mapMaybe (\(match, build) ->
      fmap (map build . sequence . map (search (n - 1)))
        (match seq))
  $ rules

atDepthAtMost :: Int -> ProofTree -> [ProofTerm]
atDepthAtMost _ (ProofTree _ (_, _) [])            = [identityFunction]
atDepthAtMost 0 _                                  = [abort]
atDepthAtMost n (ProofTree seq (match, build) pts) =
  map build . sequence $ map (atDepthAtMost (n - 1)) pts

rules = undefined
-}
-- search :: [Rule] -> Sequent -> 
