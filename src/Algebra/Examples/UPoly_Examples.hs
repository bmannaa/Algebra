module UPoly_Examples where

import Algebra.UPoly

{- To test this try:
f :: Qx
f = -7+3*x+4*x^2+x^3

fs :: Ideal Qx
fs = Id [2-3*x+x^3, -1+x^4, -1+x^6]

-- Another example:
test = member (x^2-4) (Id [x^3+x^2-4*x-4, x^3-x^2-4*x+4, x^3-2*x^2-x+2])
-}
