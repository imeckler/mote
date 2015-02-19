module Types where

import qualified Data.Map as M
import GHC
import System.IO
import UniqSupply
import Data.Time.Clock

type Hole = SrcSpan

data FileData = FileData
  { path     :: FilePath
  , modified :: UTCTime
  , hsModule :: HsModule RdrName
  }

data SlickState = SlickState
  { fileData    :: Maybe FileData
  , currentHole :: Maybe Hole
  , holesInfo   :: M.Map SrcSpan HoleInfo
  , logFile     :: Handle
  , uniq        :: UniqSupply
  }

data HoleInfo = HoleInfo
  { holeName    :: String
  , holeTypeStr :: String
  , holeEnv     :: [(String, String)] -- (ident, type)
  }
  deriving (Show)

