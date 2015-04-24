module Search.Types
  ( TransName
  , Trans(..)
  , Move
  , CutFreeProof(..)
  , Program
  , CutProof(..)
  , Term(..)
  , AnnotatedTerm(..)
  ) where

import Data.Map (Map)
import Search.Types.CutProof
import Search.Types.Basic

type Move f         = ([f], Trans f, [f]) -- (fs, t, gs) = fmap_{fs} (t at gs)
type CutFreeProof f = [Move f]
type Program f      = CutFreeProof f

