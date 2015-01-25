{-# LANGUAGE NamedFieldPuns, PatternGuards #-}
module ParseHoleMessage where

import Text.Parsec
import Text.Parsec.String
import Control.Applicative hiding (many)
import Data.Maybe
import Data.List.Split

data HoleInfo = HoleInfo
  { holeName    :: String
  , holeTypeStr :: String
  , holeEnv     :: [(String, String)] -- (ident, type)
  }
  deriving (Show)

-- Soooo brittle
identAndType :: Parser (String, String)
identAndType = do
  string "Found hole "
  holeName <- between (char openQuote) (char closeQuote) (many (satisfy (/= closeQuote)))
  string " with type: "
  holeTypeStr <- many notNewline
  return (holeName, holeTypeStr)
  where
  notNewline = satisfy (/= '\n')
  openQuote = '\8216'
  closeQuote = '\8217'

parseHoleInfo :: String -> Maybe HoleInfo
parseHoleInfo msg =
  either (const Nothing) (\(holeName, holeTypeStr) ->
    Just $ HoleInfo {holeName, holeTypeStr, holeEnv})
  $ parse identAndType "" msg
  where
  holeEnv = mapMaybe extractBinding . dropWhile (/= "Relevant bindings include") $ lines msg
  extractBinding (' ':' ':s) = case splitOn " :: " s of
    [var, ty] -> 
      case (reverse . drop 2 . dropWhile (/= '(') . reverse $ ty) of
        ""  -> Just (var, ty)
        ty' -> Just (var, ty')

    _         -> Nothing

  extractBinding _ = Nothing

