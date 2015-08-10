module Mote.Types
  ( Hole
  , FileData (..)
  , MoteState (..)
  , HoleInfo (..)
  , ErrorType (..)
  , AugmentedHoleInfo(..)
  , M
  , Ref
  , ScopeMap
  ) where

import           Control.Concurrent.MVar
import           Control.Monad.Error
import           Data.IntervalMap.FingerTree (IntervalMap)
import qualified Data.Map                    as Map
import qualified Data.Set                    as Set
import           Data.Time.Clock
import           GHC
import           System.IO
import           TcRnTypes                   (Ct (..))
import           UniqSupply
import Mote.Search.WrappedType
import Mote.Search.TypePoset
import Var (Var)

type Hole = SrcSpan

type Ref = MVar

type ScopeMap = IntervalMap SrcLoc RdrName
data FileData = FileData
  { path                 :: FilePath
  -- This is apparently stored in the ModSummary. Check it out.
  , modifyTimeAtLastLoad :: UTCTime
  , hsModule             :: HsModule RdrName
  , typecheckedModule    :: TypecheckedModule
  , holesInfo            :: Map.Map SrcSpan AugmentedHoleInfo
  , scopeMap             :: ScopeMap
  , inScopePosetData     :: (TypePoset, Var, WrappedType)
  }

data MoteState = MoteState
  { fileData    :: Maybe FileData
  , currentHole :: Maybe AugmentedHoleInfo
  , logFile     :: Handle
  , uniq        :: UniqSupply
  , argHoles    :: Set.Set Hole -- holes which are arguments to functions
  , loadErrors  :: [String]
  }

data AugmentedHoleInfo = AugmentedHoleInfo
  { holeInfo    :: HoleInfo
  -- these are computed only when requested. I would like to rely on
  -- Haskell's laziness for memoization here but the fact that suggestions
  -- are computed in a monad makes it impossible.
  , suggestions :: Maybe [(Name, Type)]
  }

data HoleInfo = HoleInfo
  { holeCt          :: Ct
  , holeEnv         :: [(Id, Type)]
  }

-- | Possible errors from the server.
data ErrorType
  = NoHole             -- ^ No hole at the current location.
  | NotInMap           -- ^ The current hole has not been loaded properly into Mote.
  | NoFile             -- ^ The given file was not loaded properly into Mote.
  | NoVariable String  -- ^ The variable with the given name does not exist.
  | TypeNotInEnv       -- ^ The type does not make sense in the current environment.
  | NoRefine           -- ^ The provided expression for refinement didn't match the hole type.
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

