module Mote.Search.Constraint where

data Implies :: [] Constraint -> [] Constraint -> * where
  Implies :: (we have "class (C1 a1 .. xn) => C2 b1 .. bn") -> Edge [C2 b1 ... bn] [C1 y1 ... yn]
  Instance :: (we have "instance C a1 .. an") -> Edge [x1 ~ a1, ... xn ~ an] [C x1 ... xn]
  Weaken :: Edge 


