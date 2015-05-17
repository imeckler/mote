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
headMay (x:_) = x

lookupExn :: (Ord k, Show k) => k -> Map k v -> v
lookupExn k = fromMaybe (error ("M.lookup failed for key: " ++ show k)) . Map.lookup k

findMap :: (a -> Maybe b) -> [a] -> Maybe b
findMap f = foldr (\x r -> case f x of { Just y -> Just y; _ -> r }) Nothing
