module Search.Util where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe

lastMay :: [a] -> Maybe a
lastMay []     = Nothing
lastMay [x]    = Just x
lastMay (_:xs) = lastMay xs

headMay :: [a] -> Maybe a
headMay [] = Nothing
headMay (x:_) = Just x

lookupExn :: (Ord k, Show k) => k -> Map k v -> v
lookupExn k = fromMaybe (error ("M.lookup failed for key: " ++ show k)) . Map.lookup k

lookupExn' :: (Ord k, Show k) => String -> k -> Map k v -> v
lookupExn' s k = fromMaybe (error (s ++ ": " ++ "M.lookup failed for key: " ++ show k)) . Map.lookup k

findMap :: (a -> Maybe b) -> [a] -> Maybe b
findMap f = foldr (\x r -> case f x of { Just y -> Just y; _ -> r }) Nothing

splittings :: [f] -> [([f],[f])]
splittings = go [] where
  go pre l@(f : fs) = (reverse pre, l) : go (f:pre) fs
  go pre [] = [(reverse pre, [])]

fineViews = concatMap (\(pre, post) -> fmap (\(x,y) -> (pre,x,y)) (splittings post)) . splittings

(|>) :: a -> (a -> b) -> b
(|>) x f = f x
