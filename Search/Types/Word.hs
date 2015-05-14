{-# LANGUAGE DeriveGeneric #-}
module Search.Types.Word where

import Data.Hashable
import Data.Bifunctor
import Data.Monoid
import GHC.Generics
import Control.Applicative
import qualified Data.List as List

data Word f o = Word [f] (Maybe o)
  deriving (Eq, Ord, Show, Generic)

instance Bifunctor Word where
  first g (Word fs mo)  = Word (Prelude.map g fs) mo
  second g (Word fs mo) = Word fs (fmap g mo)

  bimap g g' (Word fs mo) = Word (Prelude.map g fs) (fmap g' mo)

instance Monoid (Word f o) where
  mempty = Word [] Nothing

  mappend w@(Word _ (Just _)) _           = w
  mappend (Word fs Nothing) (Word fs' mo) = Word (fs ++ fs') mo

instance (Hashable f, Hashable o) => Hashable (Word f o)

length :: Word f o -> Int
length (Word fs mo) = case mo of { Just _ -> 1 + Prelude.length fs; _ -> Prelude.length fs }

fold :: (f -> s -> s) -> (o -> s -> s) -> s -> Word f o -> s
fold f g z (Word fs mo) =
  case mo of { Just o -> g o s; Nothing -> s }
  where s = foldl (flip f) z fs 

toList :: Word x x -> [x]
toList (Word xs mx) = xs ++ maybe [] (:[]) mx

map :: (a -> b) -> Word a a -> Word b b
map f = bimap f f

end :: Word a o -> Maybe o
end (Word _ mo) = mo

-- eh...
zip :: Word f o -> Word g p -> Word (f, g) (o, p)
zip (Word fs mo) (Word gs mp) = Word (Prelude.zip fs gs) (liftA2 (,) mo mp)

data InContext f o vmid vend
  = Middle [f] vmid (Word f o)
  | End [f] vend
  deriving (Eq, Ord, Show, Generic)

{-
data InContext f o vno vyesmid vyesend
  = NoO [f] vno [f]
  | YesOEnd [f] ([f], o) vyesend
  | YesOMid [f] (focus : [f]) [f] o
-}

-- I think I could make do with just InContext and view as a special case,
-- but I kept getting confused.
data View f o
  = NoO [f] {- focus -} [f] [f]
  | YesOMid [f] {- focus -} [f] [f] o
  | YesOEnd [f] {- [f] and o are focus -} ([f], o)
  deriving (Eq, Ord, Show, Generic)

instance (Hashable f, Hashable o, Hashable vmid, Hashable vend) => Hashable (InContext f o vmid vend)
instance (Hashable f, Hashable o) => Hashable (View f o)

-- type View f o = InContext f o [f] (Word f o)

-- too dumb to do this properly
views :: Word f o -> [View f o]
views (Word fs mo) = case mo of
  Nothing -> fmap (\(x,y,z) -> NoO x y z) (fineViews fs)
  Just o ->
    fmap (\(pre,mid,post) -> YesOMid pre mid post o) (fineViews fs)
    ++ fmap (\(pre, post) -> YesOEnd pre (post, o)) (splittings fs)

{-
views :: Word f o -> [View f o]
views w@(Word fs mo) =
  concatMap (\(pre, post0) ->
    End pre (Word post0 mo)
    : fmap (\(mid,post) -> Middle pre mid (Word post mo)) (splittings post0))
    (splittings fs)
-}
  {-
  End (fs, mo) () :
  concatMap (\(pre, post0) ->
    map (\(mid,post) -> Middle pre mid (post, mo)) (splittings post0))
    (splittings fs)
    -}

splittings :: [f] -> [([f],[f])]
splittings = go [] where
  go pre l@(f : fs) = (reverse pre, l) : go (f:pre) fs
  go pre [] = [(reverse pre, [])]

fineViews = concatMap (\(pre, post) -> fmap (\(x,y) -> (pre,x,y)) (splittings post)) . splittings
