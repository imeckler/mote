module Search.Types.Basic where

import TyCon

type TransName = String
data Trans f   = Trans { from :: [f], to :: [f], name :: TransName }
  deriving (Show)
