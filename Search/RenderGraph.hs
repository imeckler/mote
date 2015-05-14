{-# LANGUAGE RecordWildCards #-}
module Search.RenderGraph where

import Search.Graph
import qualified Data.Text as T
import Data.Aeson
import qualified Data.Map as M
import Data.Monoid
import qualified Data.ByteString.Lazy as BL


graphToJSON :: NaturalGraph String String -> Value
graphToJSON (NaturalGraph {..}) = 
  object
  [ T.pack "nodes" .= nodes
  , T.pack "edges" .= edges
  ]
  where
  nodeObj id lab col  = object [T.pack "id" .= id, T.pack "label" .= lab , T.pack "color" .= col ]
  edgeObj from to lab =
    object
    [ T.pack "from" .= from
    , T.pack "to" .= to
    , T.pack "label" .= lab
    , T.pack "style" .= "arrow"
    ]
  nodes =
    map (\i -> nodeObj ("in" ++ show i) "" "green") [0..(incomingCount - 1)]
    ++ map (\i -> nodeObj ("out" ++ show i) "" "red") [0..(outgoingCount - 1)]
    ++ map (\(i, vd) -> nodeObj ("real" ++ show i) (label vd) "gray") (M.toList digraph)

  edges =
    concatMap (\(v, vd) -> map (\(u,f) ->
      edgeObj ("real" ++ show v)
        (case u of { Real r -> "real" ++ show r; Dummy d -> "out" ++ show d })
        f) (outgoing vd))
      (M.toList digraph)
    ++ map (\(lab, (i, vert)) -> 
        let v = case vert of {Dummy d -> "out" ++ show d; Real r -> "real" ++ show r} in
        edgeObj ("in" ++ show i) v lab)
        (zip incomingLabels $ M.toList incomingSuccs)

graphToJS id ng = mconcat
  [ "network = new vis.Network("
  , "document.getElementById(" ,  show id , "),"
  , map (toEnum . fromEnum) . BL.unpack $ encode (graphToJSON ng)
  , ",{});"
  ]

graphsToHTML ngs =
  let js = unlines $ zipWith graphToJS (map idName [0..]) ngs
  in
  unlines
  [ "<html>"
  , "<head>"
  ,   "<style type='text/css'>"
  ,   ".network { width: 500px; height:500px; }"
  ,   "</style>"
  ,   "<script type='text/javascript' src='vis.min.js'></script>"
  ,   "<script type='text/javascript'>" ++ "function draw(){" ++ js ++ "}" ++ "</script>"
  , "</head>"
  , "<body onload='draw()'>"
  ,   unlines $ zipWith (\i ng ->
        "<div>"
        ++ "<div class='network' id=" ++ show (idName i) ++ "></div>" 
        ++ "<div>" ++ renderAnnotatedTerm (toTerm ng) ++ "</div>"
        ++ "</div>"
        ) [0..] ngs
  , "</body>"
  , "</html>"
  ]
  where
  idName i = "net" ++ show i


