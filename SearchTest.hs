{-# LANGUAGE RecordWildCards #-}
module SearchTest where

import qualified Data.Set as S
import Data.Maybe
import qualified Data.Map as M
import qualified Data.PSQueue as P

type EdgeName = String
type Name = Char
type Vertex = ([Name], [Name])

data Trans = Trans { from :: [Name], to :: [Name], transName :: String }

allNames = "LMTNG"
isTraversable = (`elem` "LMN")
isApplicative = (`elem` "LMTG")

transes :: [Trans]
transes = 
  [ Trans { from = "LM", to = "L", transName = "catMaybes"}
  , Trans { from = "", to = "L", transName = "map (\\_ -> x) ?" }
  , Trans { from = "T", to = "G", transName = "inHoleEnv" }
  , Trans { from = "", to = "N", transName = "(?, _)" }
  ]

successors :: Vertex -> Maybe [(Vertex, EdgeName)]
successors (s, t) =
  if s == t
  then Nothing
  else fmapEdge ++ sequenceREdge ++ sequenceLEdge ++ transEdges
  where
  fmapEdge
    | (cs:s', ct:t') <- (s, t), cs == ct = [((s', t'), "fmap")]
    | otherwise = []

  sequenceREdge
    | ctf:ctt:t' <- t
    , isApplicative ctf && isTraversable ctt
    = [((s, ctt:ctf:t'), "sequence-right")]
    | otherwise = []

  sequenceLEdge
    | cst:csf:s' <- s
    , isTraversable cst && isApplicative csf
    = [((csf:cst:s'), "sequence-left")]
    | otherwise = []

  transEdges =
    mapMaybe (\(Trans{..}) ->
      case (leftFromRight from s, leftFromRight to t) of
        (Just s', Just t') -> Just ((s', t'), transName)
        _                  -> Nothing
      ) transes

leftFromRight :: Eq a => u[a] -> [a] -> Maybe [a]
leftFromRight (x : xs) [] = Nothing
leftFromRight (x : xs) (y : ys)
  | x == y    = leftFromRight xs ys
  | otherwise = Nothing
leftFromRight [] ys = Just ys

dijkstra = undefined where
  maxDist = 10
  go :: M.Map Vertex (Int, (Vertex, EdgeName))
     -> M.Map Vertex (Vertex, EdgeName) -- if only the psq supported additional decorative data
     -> P.PSQ Vertex Int
     -> M.Map Vertex (Int, (Vertex, EdgeName))
  go visited onDeckPreds onDeckDists =
    case P.minView onDeckDists of
      Just (u P.:-> dist, onDeckDists') ->
        let visited' =
              M.insert u (dist, fromJust $ M.lookup u onDeckPreds) visited

            nexts = 
              if dist >= maxDist
              then []
              else
                filter (\(v, _) -> not (M.member v visited))
                $ successors u

            (onDeckPreds', onDeckDists') =
              foldl (\(ps, ds) (v, en) ->
                let ds' = P.insertWith min v (dist + 1) v ds 
                    ps' =
                      if P.lookup v ds' == Just (dist + 1)
                      then M.insert v (u,en) ps
                      else ps
                in (ps', ds'))
                (onDeckPreds, onDeckDists) nexts
        in
        go visited' onDeckPreds' onDeckDists'
      Nothing             -> visited

