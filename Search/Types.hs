{-# LANGUAGE LambdaCase, DeriveFunctor, DeriveGeneric, NamedFieldPuns #-}
module Search.Types where

import Data.Monoid
import Data.Hashable
import Data.Aeson
import GHC.Generics hiding (from, to)
import Data.Bifunctor
import Search.Types.Word

-- (fs, t, gs) = fmap_{fs} (t at gs)
-- It would be more accurate for a move to have a neighbor list
-- on the right hand side (with fogged edges) but the fogging is
-- taken care of by Canonicalize, so it is unnecessary
type Move f o = InContext f o (Trans f o) (Trans f o)

-- Really wants to be a dependent type
{-
data InWordContext f o vno vyesmid vyesend
  = NoO [f] vno [f]
  | YesOMid [f] vyesmid [f] o
  | YesOEnd [f] [f] o vyesend
-}
-- This type remains wrong... can have both Middle xs a (Word [] Nothing)
-- and End xs a

-- type WordView f o = InWordContext f o [f] [f] ()

{-
data WordView f o
  = NoO [f] [f] [f]
  | YesOMid [f] [f] [f] o -- pre, focus, post, posto
  | YesOEnd [f] o -- pre, focus
  deriving (Show)
-}

data Term
  = Id
  | Simple String
  | Compound String
  deriving (Eq, Ord, Show)

data AnnotatedTerm = AnnotatedTerm
  { unannotatedTerm :: Term
  , numHoles        :: Int
  , weight          :: Int
  }
  deriving (Eq, Ord, Show)

instance Monoid Term where
  mempty = Id

  mappend Id x = x
  mappend x Id = x
  mappend x y  = Compound (extract x ++ " . " ++ extract y) where
    extract = \case { Simple s -> s; Compound s -> s; _ -> error "Search.Types.Basic.extract: Impossible" }

instance Monoid AnnotatedTerm where
  mempty = AnnotatedTerm mempty 0 0

  mappend (AnnotatedTerm t n w) (AnnotatedTerm t' n' w') =
    AnnotatedTerm (t <> t') (n + n') (w + w')

instance Hashable Term where
  hashWithSalt s Id           = s `hashWithSalt` (0 :: Int)
  hashWithSalt s (Simple x)   = s `hashWithSalt` (1 :: Int) `hashWithSalt` x
  hashWithSalt s (Compound x) = s `hashWithSalt` (2 :: Int) `hashWithSalt` x

instance Hashable AnnotatedTerm where
  hashWithSalt s (AnnotatedTerm t _ _) = hashWithSalt s t

instance ToJSON Term where
  toJSON = \case
    Id         -> toJSON "id"
    Simple s   -> toJSON s
    Compound s -> toJSON s

instance ToJSON AnnotatedTerm where
  toJSON = toJSON . unannotatedTerm


type TransName = AnnotatedTerm
data Trans f o =
  Trans
  { from :: Word f o
  , to   :: Word f o
  , name :: TransName 
  }
  deriving (Show, Eq, Ord, Generic)

instance (Hashable f, Hashable o) => Hashable (Trans f o) where

instance Bifunctor Trans where
  bimap f g t = t { from=bimap f g (from t), to=bimap f g (to t) }

  first f t = t { from = first f (from t), to = first f (to t) }

  second g t = t { from = second g (from t), to = second g (to t) }

