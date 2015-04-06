{-# LANGUAGE RecordWildCards #-}
module SearchTest where

import qualified Data.Set as S
import Data.Maybe
import qualified Data.Map as M
import qualified Data.PSQueue as P

type Program  = String
type EdgeName = Program -> Program -- String
type Name     = Char
type Vertex   = ([Name], [Name])

data Trans = Trans { from :: [Name], to :: [Name], transName :: String }

allNames = "LMTNG"
isTraversable = (`elem` "LMN")
isApplicative = (`elem` "LMTG")

transes :: [Trans]
transes = 
  [ Trans { from = "LM", to = "L", transName = "catMaybes"}
  , Trans { from = "", to = "L", transName = "\\x -> map (const x) ?" }
  , Trans { from = "LL", to = "L", transName = "concat" }
  , Trans { from = "T", to = "G", transName = "inHoleEnv" }
  , Trans { from = "", to = "N", transName = "\\x -> (?, x)" }
  ]

-- Really should do something special when they're equal.
successors :: Vertex -> [(Vertex, EdgeName)]
successors (s, t) =
  fmapEdge ++ sequenceREdge ++ sequenceLEdge ++ transEdges
  where
  fmapEdge
    | (cs:s', ct:t') <- (s, t), cs == ct
    = [((s', t'), \p -> "fmap{" ++ [cs] ++ "}" ++ "(" ++ p ++ ")")]
    | otherwise = []

  sequenceREdge
    | ctf:ctt:t' <- t
    , isApplicative ctf && isTraversable ctt
    = [((s, ctt:ctf:t'), \p -> "sequenceA . " ++ p)] -- "sequence-right")]
    | otherwise = []

  sequenceLEdge
    | cst:csf:s' <- s
    , isTraversable cst && isApplicative csf
    = [((csf:cst:s', t), \p -> p ++ ". sequenceA")] -- "sequence-left")]
    | otherwise = []

  transEdges =
    concatMap (\(Trans{..}) ->
      let rrule =
            case leftFromRight to t of
              Just t' -> [((s, from ++ t'), \p -> transName ++ " . " ++ p)] -- transName ++ "-right")]
              Nothing -> []
          lrule =
            case leftFromRight from s of
              Just s' -> [((to ++ s', t), \p -> p ++ " . " ++ transName)] -- transName ++ "-left")]
              Nothing -> []
      in
      rrule ++ lrule)
      transes

leftFromRight :: Eq a => [a] -> [a] -> Maybe [a]
leftFromRight (x : xs) [] = Nothing
leftFromRight (x : xs) (y : ys)
  | x == y    = leftFromRight xs ys
  | otherwise = Nothing
leftFromRight [] ys = Just ys

dijkstra
  :: Vertex -> M.Map Vertex (Int, (Vertex, EdgeName))
dijkstra init = 
  let nexts = successors init 
  in
  go M.empty
    (M.fromList . map (\(v, en) -> (v, (init, en))) $ nexts)
    (P.fromList . map (\(v, _) -> v P.:-> 1) $ nexts)
  where
  maxDist = 8
  go visited onDeckPreds onDeckDists =
    case P.minView onDeckDists of
      Just (u P.:-> dist, onDeckDists') ->
        let visited' =
              M.insert u (dist, fromJust $ M.lookup u onDeckPreds) visited

            nexts = 
              if dist >= maxDist
              then []
              else if let (s, t) = u in length s > 5 || length t > 5
              then []
              else
                filter (\(v, _) -> not (M.member v visited'))
                $ successors u

            (onDeckPreds', onDeckDists'') =
              foldl (\(ps, ds) (v, en) ->
                let ds' = P.insertWith min v (dist + 1) ds 
                    ps' =
                      if P.lookup v ds' == Just (dist + 1)
                      then M.insert v (u,en) ps
                      else ps
                in (ps', ds'))
                (onDeckPreds, onDeckDists') nexts
        in
        go visited' onDeckPreds' onDeckDists''
      Nothing             -> visited -- visited

prove :: Vertex -> Program
prove init = go "id" ("", "") where
  d        = dijkstra init
  go acc v =
    case M.lookup v d of
      Just (_, (pre, en)) -> go (en acc) pre
      Nothing             -> acc

-- for prove ("TM", "GLN"), got
-- inHoleEnv . fmap{T}(catMaybes . \x -> map (const x) ? . fmap{M}(\x -> (?, x) . id))
-- wanted
-- fmap catMaybes 
-- . sequenceA
-- . (\x -> map (fmap (fmap (cmap ?)) . inHoleEnv . const x) ?)
-- ==
-- fmap catMaybes 
-- . sequenceA
-- . (\x -> map (\_ -> fmap (fmap (cmap ?)) (inHoleEnv x)) ?)
--
-- or possibly
-- inHoleEnv . fmap catMaybes . sequenceA . map (\x -> map (\_ -> (fmap (fmap (\y -> (?,y)))) x) ?)
-- ==
-- inHoleEnv . fmap catMaybes . sequenceA . (\x -> map (fmap (fmap (\y -> (?, y))) . const x) ?)
--
-- want cmaps close to the seed data (so that the data can depend on some
-- stuff)
