{-# LANGUAGE LambdaCase #-}
module Main where

import Control.Monad.Error
import Search.Types
import Search.Graph
import Slick.Types
import TyCon
import TypeRep
import Slick.ReadType
import Control.Applicative
import qualified Data.List as List
import System.Environment (getArgs)

import qualified Data.HashSet as HashSet

type F = String

list         = "List"
may          = "Maybe"
io           = "IO"
eithererr    = "Either ErrorType"
tcrn         = "TcRn"
ghc          = "Ghc"
messagesprod = "(,) ErrUtils.Mesages"
mm           = "ErrorT ErrorType Ghc"

monads       = [list, may, io, eithererr, tcrn, ghc, mm]
traversables = [list, may, eithererr, messagesprod]
applicatives = [list, may, io, eithererr, tcrn, ghc, mm]

joint f   = Trans { from = [f,f], to = [f], name = Simple "join" }
returnt f   = Trans { from = [], to = [f], name = Simple "return" }
sequ t f = Trans {from = [t, f], to = [f, t], name = Simple "sequence" }

transes :: [Trans F]
transes =
  concatMap (\x -> [joint x {-, returnt x -}]) monads
  ++ liftA2 sequ traversables applicatives
  ++
  [ Trans { from = [list, may], to = [list], name = Simple "catMaybes" }
  , Trans { from = [ghc], to = [io], name = Compound "runGhc _" }
  , Trans { from = [mm], to = [eithererr, ghc], name = Simple "runErrorT" }
  , Trans { from = [tcrn], to = [io, messagesprod, may], name = Compound "runTcInteractive _" }
  , Trans { from = [messagesprod], to = [], name = Simple "snd" }
  , Trans { from = [may], to = [mm], name = Simple "maybeErr" }
  , Trans { from = [list], to = [mm], name = Simple "headErr" }
  , Trans { from = [tcrn], to = [mm], name = Compound "inHoleEnv _ _" }
  , Trans { from = [eithererr], to = [may], name = Compound "either (const Nothing) Just" }
  ]

main :: IO ()
main = do
  (nStr:args) <- getArgs
  case args of
    "f":_ -> print (f (read nStr))
    _     -> print (g (read nStr))
  where
  from = [list, may, mm]
  to   = [io,list]
  g n = HashSet.size $ graphsOfSizeAtMost transes n from to
  f n =
    HashSet.size . HashSet.fromList . map programToNaturalGraph
    $ programsOfLengthAtMost transes n from to

