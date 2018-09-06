module Algebra.Examples.EllipticCurve_Examples where

import Algebra.EllipticCurve
import Algebra.Structures.Coherent
import Algebra.Structures.Rings
import Algebra.Structures.PruferDomains
import Algebra.Ideals
import Algebra.Q
import Algebra.UPoly

-- Examples of computing the intersection of two ideals
ex1 = Id [C (x,zero)] `intersectionPD` Id [C (one,neg one)]

ex2 = Id [ C (x,zero)] `intersectionPD` Id [ C (2, neg one)]

-- Compute PLM
ex3 = computePLM_PD (Id [C (x,zero),C (one,neg one)])
