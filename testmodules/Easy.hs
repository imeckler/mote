module Easy where

import Data.Traversable
import qualified Data.List as List
import Control.Monad.Error
import Data.Maybe

eitherToMaybe :: Either String a -> Maybe a
eitherToMaybe = either (const Nothing) Just

