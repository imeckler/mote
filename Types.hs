module Types where

import qualified Data.Map as M
import qualified Data.Set as S
import GHC
import System.IO
import UniqSupply
import Data.Time.Clock
import Control.Monad.Error

type Hole = SrcSpan

data FileData = FileData
  { path                 :: FilePath
  , modifyTimeAtLastLoad :: UTCTime
  , typecheckedModule    :: TypecheckedModule
  , hsModule             :: HsModule RdrName
  }

data SlickState = SlickState
  { fileData    :: Maybe FileData
  , currentHole :: Maybe Hole
  , holesInfo   :: M.Map SrcSpan HoleInfo
  , logFile     :: Handle
  , uniq        :: UniqSupply
  , argHoles    :: S.Set Hole -- holes which are arguments to functions
  }

-- TODO: Maybe just comute all the types up front
data HoleInfo = HoleInfo
  { holeName    :: String
  , holeTypeStr :: String
  , holeEnv     :: [(String, String)] -- (ident, type)
  }
  deriving (Show)


-- | Possible errors from the server.
data ErrorType
  = NoHole             -- ^ No hole at the current location.
  | NotInMap           -- ^ The current hole has not been loaded properly into Slick.
  | NoFile             -- ^ The given file was not loaded properly into Slick.
  | NoVariable String  -- ^ The variable with the given name does not exist.
  | TypeNotInEnv       -- ^ The type does not make sense in the current environment.
  | NoRefine           -- TODO: Figure out what this means :þ ("Could not refine.")
  | NoHoleInfo         -- ^ Information for the current hole was not loaded properly.
  | ParseError String  -- ^ A parse error with the given message.
  | GHCError String    -- ^ An error (and message) directly from GHC.
  | Unsupported String -- ^ The feature with the given name is not supported (yet).
  | OtherError String  -- ^ Some other error, with the given error message.
  | UnknownError       -- ^ An error that doesn't even have an error message.

instance Show ErrorType where
  show NoHole                = "No hole at the current location."
  show NotInMap              = "Hole not loaded into map."
  show NoFile                = "File not loaded."
  show (NoVariable var)      = "Variable `" ++ var ++ "' not found."
  show TypeNotInEnv          = "The type does not make sense in the current environment."
  show NoRefine              = "Could not refine."
  show NoHoleInfo            = "Information for the current hole was not loaded properly."
  show (ParseError msg)      = "Parse error: " ++ msg
  show (GHCError msg)        = "GHC error: " ++ msg
  show (Unsupported feature) = feature ++ " is not supported yet."
  show (OtherError msg)      = msg
  show UnknownError          = "Unknown error."

instance Error ErrorType where
  noMsg = UnknownError
  strMsg = OtherError

type M = ErrorT ErrorType Ghc
