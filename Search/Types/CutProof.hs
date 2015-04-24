module Search.Types.CutProof where

import Search.Types.Basic

-- This essentially corresponds to Haskell terms, but with explicit labels
-- on fmaps and such
-- TODO: Might want to include sequents in recursive occurences
data CutProof f
  = FMap f (CutProof f)
  | At [f] (CutProof f)
  | Cut (CutProof f) {- A -> B -} (CutProof f) {- B -> C -}
  | Axiom (Trans f)

