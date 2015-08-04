{-# LANGUAGE TupleSections, ScopedTypeVariables, LambdaCase, NamedFieldPuns #-}
module Mote.Search.Poset where

import qualified Data.HashTable.IO as HashTable
import Data.Hashable (Hashable)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad (filterM)
import Control.Applicative
import Data.Maybe (isJust, catMaybes)
import Data.Monoid ((<>))
import qualified Data.Set as Set
import qualified Data.List as List

import Outputable (Outputable, ppr, ptext)
import FastString (sLit)

import Mote.Util

type PartialOrdering
  = Maybe Ordering

flipOrder :: Ordering -> Ordering
flipOrder ord =
  case ord of
    LT ->
      GT

    GT ->
      LT
    
    EQ ->
      EQ

pairs :: [a] -> [(a, a)]
pairs []     = []
pairs (x:xs) = map (x,) xs ++ pairs xs

data ElementData k v =
  ElementData
  { above :: Set.Set k
  , below :: Set.Set k
  , value :: v
  }
  deriving (Show)

type HashTable k v
  = HashTable.BasicHashTable k v

type PosetStore k v =
  HashTable k (ElementData k v)

-- n^2 don't care
fromList
  :: (MonadIO m, Hashable k, Ord k, Monoid v)
  => (k -> k -> m PartialOrdering)
  -> [(k, v)]
  -> m (PosetStore k v)
fromList cmp xs = do
  table_tmp <- liftIO (HashTable.new :: IO (HashTable k (HashTable k Ordering, v)))
  let
    getCreateSubTable (k, v) =
      HashTable.lookup table_tmp k >>= \case
        Just table_and_val ->
          return table_and_val

        Nothing -> do
          tbl_k <- HashTable.new
          HashTable.insert table_tmp k (tbl_k, v)
          return (tbl_k, v)

  mapM_ (\(x@(k_x, _), y@(k_y, _)) -> do
    pord <- cmp k_x k_y
    case pord of
      Nothing ->
        return ()

      Just o ->
        liftIO $ do
          (tbl_x, _) <- getCreateSubTable x
          (tbl_y, _) <- getCreateSubTable y
          HashTable.insert tbl_x k_y o
          HashTable.insert tbl_y k_x (flipOrder o))
    (pairs xs)

  table <- liftIO HashTable.new

  let
    { getCreateSubTable (k, v) =
      HashTable.lookup table k >>= \case
        Just eltData ->
          return eltData

        Nothing -> do
          let
            eltData =
              ElementData { above = Set.empty, below = Set.empty, value = v }
          HashTable.insert table k eltData
          return eltData

    -- This is what we in the business call a very stupid algorithm.
    -- Would be better to "contract equality edges".
    ; go seen xs =
      case xs of
        [] ->
          return ()

        (k_x, (tbl_x, val_x)) : xs' ->
          if k_x `Set.member` seen
          then go seen xs'
          else do
            ys <- HashTable.toList tbl_x
            let (bel, eq, abv) = partition ys
            mayVals <- mapM (fmap (fmap snd) . HashTable.lookup table_tmp) eq
            HashTable.insert table k_x
              (ElementData
              { above = Set.fromList abv
              , below = Set.fromList bel
              , value = val_x <> mconcat (catMaybes mayVals)
              })
            go (List.foldl' (flip Set.insert) seen eq) xs'
    }

  liftIO (go Set.empty =<< HashTable.toList table_tmp)

  return table
  where
  partition ys =
    case ys of
      [] ->
        ([], [], [])
      (k_y, o_y) : ys' ->
        let (bel, eq, abv) = partition ys' in
        case o_y of
          -- x < y
          LT ->
            (bel, eq, k_y : abv)
          EQ ->
            (bel, k_y : eq, abv)
          -- y < x
          GT ->
            (k_y : bel, eq, abv)

-- tbl ! x ! y === compare x y

minimalElements :: (Ord k, Hashable k) => PosetStore k v -> IO [(k, ElementData k v)]
minimalElements =
  HashTable.foldM (\ms x@(_k_x, eltData_x) ->
    return
      (if isMinimal eltData_x
      then x : ms
      else ms))
    []
  where
  isMinimal (ElementData {above}) = Set.null above

