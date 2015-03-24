{-# LANGUAGE NamedFieldPuns, PatternGuards, QuasiQuotes #-}
module Slick.ParseHoleMessage where

import           Control.Applicative hiding (many)
import           Data.Char             (isSpace)
import           Data.List.Split       (splitOn)
import           Data.Maybe            (mapMaybe)
import           Text.Parsec
import           Text.Parsec.String
import           Text.Regex.PCRE.Heavy

import           Slick.Types

-- Soooo brittle
identAndType :: Parser (String, String)
identAndType = do
  string "Found hole "
  holeName <- between (char openQuote) (char closeQuote) (many (satisfy (/= closeQuote)))
  skipMany1 space
  string "with type:"
  holeTypeStr <- unwords <$> many (skipMany1 space *> aLine)
  return (holeName, holeTypeStr)
  where
  notNewline = satisfy (/= '\n')
  aLine = many notNewline <* char '\n'
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
    , isSymbol var
      = Just (var, gsub [re|\(bound at.*?\)|] "" ty)
    | otherwise = Nothing

  isSymbol = all (not . isSpace)

