module Algebra.Examples.Z_Examples where

import Algebra.Z
import Algebra.Structures.Coherent
import Algebra.Structures.BezoutDomains
import Algebra.Matrix
import Algebra.Ideals

-- Principal ideals
ex1 :: Ideal Z
ex1 = Id [4,6]

-- Intersection
ex2 :: (Ideal Z,[[Z]],[[Z]])
ex2 = Id [2] `intersectionB` Id [2,3]

-- Equations
ex3 = Vec [1,2,3]

m = M [Vec [1,2],Vec [2,4]]
b = Vec [1,2]
