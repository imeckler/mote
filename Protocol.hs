{-# LANGUAGE LambdaCase, ViewPatterns, OverloadedStrings #-}
module Protocol where

import qualified Data.Vector as V
import qualified Data.Text as T
import Data.Aeson hiding (Error)
import Control.Applicative
import Control.Monad

type Pos  = (Int, Int)
type Span = (Pos, Pos)
data ToClient
  = Replace Span FilePath String
  | SetInfoWindow String
  | SetCursor Pos
  | Print String
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
    where
    str x = x :: String

type Var = String

data ClientState = ClientState { path :: FilePath, cursorPos :: (Int, Int) }
  deriving (Show)

instance FromJSON ClientState where
  parseJSON (Object v) = ClientState <$> v .: "path" <*> v .: "cursorPos"
  parseJSON _          = mzero

-- Things could be a bit more efficient if the client held on to which hole
-- they're in. Probably not necessary, but if things are slow, consider
-- it.

-- next big thing: in hole suggestions.
-- let's say my goal type is SrcLoc.
-- Functions are suggested whose target type is SrcLoc
-- and whose arguments are in the environment. Perhaps
-- do something linear. Also maybe use hoogle
-- 
data FromClient
  = Load FilePath
  | EnterHole ClientState
  | NextHole ClientState
  | PrevHole ClientState
  | GetEnv ClientState
  | Refine String ClientState
  | GetType String
  | CaseFurther Var ClientState 
  | CaseOn String
  | SendStop
  deriving (Show)

instance FromJSON FromClient where
  parseJSON = \case
    Array a                                     -> case V.toList a of
      [String "Load", String path]              -> return (Load (T.unpack path))
      [String "CaseFurther", String var, state] -> CaseFurther (T.unpack var) <$> parseJSON state
      [String "EnterHole", state]               -> EnterHole <$> parseJSON state
      [String "NextHole", state]                -> NextHole <$> parseJSON state
      [String "PrevHole", state]                -> PrevHole <$> parseJSON state
      [String "GetEnv", state]                  -> GetEnv <$> parseJSON state
      [String "Refine", String expr, state]     -> Refine (T.unpack expr) <$> parseJSON state
      [String "GetType", String e]              -> return . GetType $ T.unpack e
      [String "SendStop"]                       -> return SendStop
      _                                         -> mzero

