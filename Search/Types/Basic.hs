{-# LANGUAGE LambdaCase, DeriveFunctor #-}
module Search.Types.Basic where

import TyCon
import Data.Monoid
import Data.Hashable
import Data.Aeson

data Term
  = Id
  | Simple String
  | Compound String
  deriving (Eq, Ord)

instance Monoid Term where
  mempty = Id

  mappend Id x = x
  mappend x Id = x
  mappend x y  = Compound (extract x ++ " . " ++ extract y) where
    extract = \case { Simple s -> s; Compound s -> s }

instance Show Term where
  show = \case
    Id         -> "id"
    Simple s   -> s
    Compound s -> s

instance Hashable Term where
  hashWithSalt s Id           = s `hashWithSalt` (0 :: Int)
  hashWithSalt s (Simple x)   = s `hashWithSalt` (1 :: Int) `hashWithSalt` x
  hashWithSalt s (Compound x) = s `hashWithSalt` (2 :: Int) `hashWithSalt` x

instance ToJSON Term where
  toJSON = \case
    Id         -> toJSON "id"
    Simple s   -> toJSON s
    Compound s -> toJSON s


type TransName = Term
data Trans f   = Trans { from :: [f], to :: [f], name :: TransName }
  deriving (Show, Functor)

