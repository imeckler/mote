{-# LANGUAGE LambdaCase, OverloadedStrings #-}
module Mote.Protocol where

import           Control.Applicative
import           Control.Monad
import           Data.Aeson          hiding (Error)
import qualified Data.Text           as T
import qualified Data.Vector         as V

type Pos  = (Int, Int)
type Span = (Pos, Pos)

data ToClient
  = Replace Span FilePath String
  | JSON Value
  | Insert Pos FilePath String
  | SetInfoWindow String
  | SetCursor Pos
  | Ok
  | Error String
  | Stop
  deriving (Show)

instance ToJSON ToClient where
  toJSON = \case
    Replace sp p t  -> Array $ V.fromList [toJSON (str "Replace"), toJSON sp, toJSON p, toJSON t]
    SetInfoWindow t -> Array $ V.fromList [toJSON (str "SetInfoWindow"), toJSON t]
    SetCursor pos   -> Array $ V.fromList [toJSON (str "SetCursor"), toJSON pos]
    Ok              -> Array $ V.fromList [toJSON (str "Ok")]
    Error t         -> Array $ V.fromList [toJSON (str "Error"), toJSON t]
    Stop            -> Array $ V.fromList [toJSON (str "Stop")]
    Insert pos p t  -> Array $ V.fromList [toJSON (str "Insert"), toJSON pos, toJSON p, toJSON t]
    JSON v          -> Array $ V.fromList [toJSON (str "JSON"), toJSON v]
    where
    str x = x :: String

type Var = String

data ClientState = ClientState { path :: FilePath, cursorPos :: (Int, Int) }
  deriving (Show)

instance FromJSON ClientState where
  parseJSON (Object v) = ClientState <$> v .: "path" <*> v .: "cursorPos"
  parseJSON _          = mzero

data HoleInfoOptions = HoleInfoOptions
  -- If this flag is true, the response to the GetHoleInfo message is
  -- a json object with the following format
  -- { "environment" : [ {"name" : String, "type" : String}* ]
  -- , "suggestions" : [ {"name" : String, "type" : String}* ]
  -- , "goal"        : {"name" : String, "type" : String}
  -- }
  { sendOutputAsData :: Bool
  -- The suggestions field is only present if withSuggestions is true
  , withSuggestions  :: Bool
  }
  deriving (Show)

instance FromJSON HoleInfoOptions where
  parseJSON = \case
    Object v -> HoleInfoOptions <$> v .: "sendOutputAsData" <*> v .: "withSuggestions"
    _        -> mzero

data FromClient
  = Load FilePath
  | EnterHole ClientState
  | NextHole ClientState
  | PrevHole ClientState
  | GetHoleInfo ClientState HoleInfoOptions
  | Refine String ClientState
  | GetType String
  | CaseFurther Var ClientState
  | CaseOn String ClientState
  | SendStop
  | Search [String] [String]
  deriving (Show)

instance FromJSON FromClient where
  parseJSON = \case
    Array a                                     -> case V.toList a of
      [String "Load", String path]              -> return (Load (T.unpack path))
      [String "CaseFurther", String var, state] -> CaseFurther (T.unpack var) <$> parseJSON state
      [String "CaseOn", String expr, state]     -> CaseOn (T.unpack expr) <$> parseJSON state
      [String "EnterHole", state]               -> EnterHole <$> parseJSON state
      [String "NextHole", state]                -> NextHole <$> parseJSON state
      [String "PrevHole", state]                -> PrevHole <$> parseJSON state
      [String "GetHoleInfo", state, hiOpts]     -> GetHoleInfo <$> parseJSON state <*> parseJSON hiOpts
      [String "Refine", String expr, state]     -> Refine (T.unpack expr) <$> parseJSON state
      [String "GetType", String e]              -> return . GetType $ T.unpack e
      [String "SendStop"]                       -> return SendStop
      [String "Search", src, trg]               -> Search <$> parseJSON src <*> parseJSON trg
      _                                         -> mzero
    _                                           -> mzero

