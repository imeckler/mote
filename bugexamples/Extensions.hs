{-# LANGUAGE DeriveFunctor, RankNTypes #-}
module Extensions where

data T a = T a
  deriving (Functor)

x :: (forall a. T a) -> Int
x = \ _ -> 3
