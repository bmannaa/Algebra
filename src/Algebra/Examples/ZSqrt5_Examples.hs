module Algebra.Examples.ZSqrt5_Examples where

import Algebra.Structures.Coherent
import Algebra.Structures.Rings
import Algebra.Structures.PruferDomains
import Algebra.Ideals
import Algebra.Z
import Algebra.ZSqrt5

-- Examples of computing the intersection of two ideals
ex1 = Id [ZSqrt5 (2,0)] `intersectionPD` Id [ZSqrt5 (1,-1)]
