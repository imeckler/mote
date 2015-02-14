module Types where

import qualified Data.Map as M
import GHC
import System.IO
import UniqSupply

type Hole = SrcSpan

data SlickState = SlickState
  { fileData    :: Maybe (FilePath, HsModule RdrName)
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

