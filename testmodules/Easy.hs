module Easy where

import Data.Traversable
import qualified Data.List as List
import Control.Monad.Error
import Data.Maybe
import qualified Data.ByteString
import GhcMonad

-- TODO: Problems with type aliases...
data FakeFilePath = FakeFilePath

fakeReadFile :: FakeFilePath -> IO Data.ByteString.ByteString
fakeReadFile = undefined

eitherToMaybe :: Either String a -> Maybe a
eitherToMaybe = either (const Nothing) Just

