{-# LANGUAGE LambdaCase, DeriveFunctor, DeriveGeneric #-}
module Search.Types where

import Data.Monoid
import Data.Hashable
import Data.Aeson
import GHC.Generics
import Data.Bifunctor

-- (fs, t, gs) = fmap_{fs} (t at gs)
type Move f o = InWordContext f o (Trans f o) (Trans f o)

-- Really wants to be a dependent type
{-
data InWordContext f o vno vyesmid vyesend
  = NoO [f] vno [f]
  | YesOMid [f] vyesmid [f] o
  | YesOEnd [f] [f] o vyesend
-}
-- This type remains wrong... can have both Middle xs a (Word [] Nothing)
-- and End xs a
data InWordContext f o vmid vend
  = Middle [f] vmid (Word f o)
  | End [f] vend
  deriving (Eq, Ord, Show, Generic)


type WordView f o = InWordContext f o [f] (Word f o)
-- type WordView f o = InWordContext f o [f] [f] ()

{-
data WordView f o
  = NoO [f] [f] [f]
  | YesOMid [f] [f] [f] o -- pre, focus, post, posto
  | YesOEnd [f] o -- pre, focus
  deriving (Show)
-}
instance (Hashable f, Hashable o, Hashable vmid, Hashable vend) => Hashable (InWordContext f o vmid vend)

data Term
  = Id
  | Simple String
  | Compound String
  deriving (Eq, Ord, Show)

data AnnotatedTerm = AnnotatedTerm
  { unannotatedTerm :: Term
  , numHoles        :: Int
  }
  deriving (Eq, Ord, Show)

instance Monoid Term where
  mempty = Id

  mappend Id x = x
  mappend x Id = x
  mappend x y  = Compound (extract x ++ " . " ++ extract y) where
    extract = \case { Simple s -> s; Compound s -> s; _ -> error "Search.Types.Basic.extract: Impossible" }

instance Monoid AnnotatedTerm where
  mempty                                            = AnnotatedTerm mempty 0
  mappend (AnnotatedTerm t n) (AnnotatedTerm t' n') = AnnotatedTerm (t <> t') (n + n')

instance Hashable Term where
  hashWithSalt s Id           = s `hashWithSalt` (0 :: Int)
  hashWithSalt s (Simple x)   = s `hashWithSalt` (1 :: Int) `hashWithSalt` x
  hashWithSalt s (Compound x) = s `hashWithSalt` (2 :: Int) `hashWithSalt` x

instance Hashable AnnotatedTerm where
  hashWithSalt s (AnnotatedTerm t _) = hashWithSalt s t

instance ToJSON Term where
  toJSON = \case
    Id         -> toJSON "id"
    Simple s   -> toJSON s
    Compound s -> toJSON s

instance ToJSON AnnotatedTerm where
  toJSON = toJSON . unannotatedTerm

data Word f o = Word [f] (Maybe o)
  deriving (Eq, Ord, Show, Generic)

instance Bifunctor Word where
  first g (Word fs mo)  = Word (map g fs) mo
  second g (Word fs mo) = Word fs (fmap g mo)

instance Monoid (Word f o) where
  mempty = Word [] Nothing

  mappend w@(Word _ (Just _)) _           = w
  mappend (Word fs Nothing) (Word fs' mo) = Word (fs ++ fs') mo

instance (Hashable f, Hashable o) => Hashable (Word f o)

wordLength :: Word f o -> Int
wordLength (Word fs mo) = case mo of { Just _ -> 1 + length fs; _ -> length fs }

foldWord :: (f -> s -> s) -> (o -> s -> s) -> s -> Word f o -> s
foldWord f g z (Word fs mo) =
  case mo of { Just o -> g o s; Nothing -> s }
  where s = foldl (flip f) z fs 

type TransName = AnnotatedTerm
data Trans f o =
  Trans
  { from :: Word f o
  , to   :: Word f o
  , name :: TransName 
  }
  deriving (Show)

