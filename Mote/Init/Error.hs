{-# LANGUAGE DeriveDataTypeable #-}

module Mote.Init.Error where

import Data.Typeable
import Exception
import qualified Control.Monad.Error.Class

data Error
  = Unknown
  -- ^ Unknown error
  | Other String
  -- ^ Some Error with a message. These are produced mostly by
  -- 'fail' calls on GhcModT.
  | IOException IOException
  -- ^ IOExceptions captured by GhcModT's MonadIO instance
  | CabalConfigure Error
  -- ^ Configuring a cabal project failed.
  | CabalFlags Error
  -- ^ Retrieval of the cabal configuration flags failed.
  | Process [String] Error
  -- ^ Launching an operating system process failed. The first
  -- field is the command.
  | NoCabalFile
  -- ^ No cabal file found.
  | TooManyCabalFiles [FilePath]
  -- ^ Too many cabal files found.
  deriving (Eq,Show,Typeable)

instance Exception Error

instance Control.Monad.Error.Class.Error Error where
    noMsg = Unknown
    strMsg = Other
