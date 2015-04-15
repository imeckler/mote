module CutElimination where

import Search.Types

eliminateCut :: CutProof -> CutFreeProof
eliminateCut cp = case cp of
  FMap f cp  -> _
  At f cp    -> _
  Cut cp cp' -> _
  Axiom t    -> _
