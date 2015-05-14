{-# LANGUAGE BangPatterns, LambdaCase #-}
module Search.Graph.Types where

import Search.Types
import Data.Hashable
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State
import Data.Maybe
import qualified Search.Types.Word as Word
import Search.Types.Word (Word)
import qualified Search.Graph.Types.NeighborList
import Search.Graph.Types.NeighborList (NeighborList(..))
import Search.Graph.Types.Vertex
import qualified Data.List as List

data VertexData f o = VertexData
  { label    :: TransName
  -- We store both the incoming and the outgoing vertices (in the proper
  -- order!) at every vertex to make traversal and obtaining the bimodal
  -- ordering easier. 
  , incoming :: NeighborList f o
  , outgoing :: NeighborList f o
  }
  deriving (Show, Eq)
-- Invariant: The incoming dummys are labeled 0 to incomingCount - 1 and
-- the outgoing dummys are labeled 0 to outgoingCount - 1
data NaturalGraph f o = NaturalGraph
  { incomingLabels :: Word f o
  , incomingSuccs  :: Map DummyVertex (Foggy Vert)
--  , incomingCount  :: Int

  , outgoingPreds  :: Map DummyVertex (Foggy Vert)
--  , outgoingCount  :: Int

  , digraph        :: Map Vertex (VertexData f o)
  }
  deriving (Show)

instance (Hashable f, Hashable o) => Eq (NaturalGraph f o) where
  (==) g1 g2 = hashWithSalt 0 g1 == hashWithSalt 0 g2 && hashWithSalt 10 g1 == hashWithSalt 10 g2

instance (Hashable f, Hashable o) => Hashable (NaturalGraph f o) where
  hashWithSalt = hashWithSaltGraph

-- isomorphic graphs will hash to the same value
-- TODO: There's either a bug in this or in isomorphic. There are more
-- unique hashes then the length of the nub by isomorphic
hashWithSaltGraph :: (Hashable f, Hashable o) => Int -> NaturalGraph f o -> Int
hashWithSaltGraph s ng =
  let vs         = M.elems $ incomingSuccs ng
      (s', _, _) =
        execState go
        ( s
        , S.fromList (mapMaybe (\case {Clear v -> Just v; _ -> Nothing}) vs)
        , vs
        )
  in s'
  where
  g  = digraph ng
  -- TODO: Possibly the states should just be S.Set Vert
  go :: State (Int, S.Set Vert, [Foggy Vert]) ()
  go = do
    (s, pushed, next) <- get
    case next of
      []                -> return ()

      CoveredInFog : next' -> put (s `hashWithSalt` (0::Int), pushed, next')

      (Clear (Dummy d) : next') ->
        put (s `hashWithSalt` d, pushed, next') >> go

      (Clear (Real v) : next') -> do
        let Just vd    = M.lookup v g
            s0         = s `hashWithSalt` label vd

            (s1, new0) =
              case incoming vd of
                WithFogged pre w ->
                  let (s', new') = List.foldl' (flip f) (s0, []) pre
                  in
                  (Word.fold (flip hashWithSalt) (flip hashWithSalt) s' w, new')

                NoFogged w -> Word.fold f f (s0, []) w
            
            -- Word.fold f' f' (Word.fold f f (s',[]) (incoming vd)) (outgoing vd)
            -- -- foldl f' (foldl f (s',[]) (incoming vd)) (outgoing vd)

            (s2, new1) =
              case outgoing vd of
                WithFogged pre w ->
                  let (s', new') = List.foldl' (flip f') (s1,new0) pre
                  in
                  (Word.fold (flip hashWithSalt) (flip hashWithSalt) s' w, new')

                NoFogged w -> Word.fold f' f' (s1,new0) w

            pushed'    = foldl (\s x -> S.insert x s) pushed new1
        put (s2, pushed', map Clear new1 ++ next')
        go
        where
        -- slideDown :: NeighborList f o -> (Int, [Vert]) -> (Int, [Vert])

        -- We don't push incoming dummies.
        f :: Hashable a => (Vert, a) -> (Int, [Vert]) -> (Int, [Vert])
        f (x,lab) (!salt, !xs) =
          ( salt `hashWithSalt` lab
          , case x of { Dummy _ -> xs; _ -> if x `S.member` pushed then xs else x:xs })

        f' :: Hashable a => (Vert, a) -> (Int, [Vert]) -> (Int, [Vert])
        f' (x,lab) (!salt, !xs)  =
          ( salt `hashWithSalt` lab
          , if x `S.member` pushed then xs else x:xs )

