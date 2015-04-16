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
import Data.Either (isRight)

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

joint f   = Trans { from = [f,f], to = [f], name = "join" }
returnt f   = Trans { from = [], to = [f], name = "return" }
sequ t f = Trans {from = [t, f], to = [f, t], name = "sequence" }

transes :: [Trans F]
transes =
  concatMap (\x -> [joint x {-, returnt x -}]) monads
  ++ liftA2 sequ traversables applicatives
  ++
  [ Trans { from = [list, may], to = [list], name = "catMaybes" }
  , Trans { from = [ghc], to = [io], name = "runGhc _" }
  , Trans { from = [mm], to = [eithererr, ghc], name = "runErrorT" }
  , Trans { from = [tcrn], to = [io, messagesprod, may], name = "runTcInteractive _" }
  , Trans { from = [messagesprod], to = [], name = "snd" }
  , Trans { from = [may], to = [mm], name = "maybeErr" }
  , Trans { from = [list], to = [mm], name = "headErr" }
  , Trans { from = [tcrn], to = [mm], name = "inHoleEnv _ _" }
  ]

main :: IO ()
main =
  mapM_ (print . f) [1..]
  where
  f n =
    let { gs = map programToNaturalGraph $ programsOfLengthAtMost transes n [list, may,tcrn] [io,list]
        ; a = List.genericLength (List.nubBy isomorphic gs)
        ; b = List.genericLength gs }
    in (a, b)

