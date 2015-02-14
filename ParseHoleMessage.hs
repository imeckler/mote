{-# LANGUAGE NamedFieldPuns, PatternGuards #-}
module ParseHoleMessage where

import Text.Parsec
import Text.Parsec.String
import Control.Applicative hiding (many)
import Data.Maybe
import Data.List.Split
import Types
import Data.Char

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
  extractBinding line
    | (' ':' ':s) <- line
    , [var, ty]   <- splitOn " :: " s
    , isIdent var
      = case (reverse . drop 2 . dropWhile (/= '(') . reverse $ ty) of
          ""  -> Just (var, ty)
          ty' -> Just (var, ty')

    | otherwise = Nothing

  isIdent (c:s) = isAlpha c && all isAlphaNum s

