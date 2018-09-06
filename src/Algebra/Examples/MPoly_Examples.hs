module MPoly_Examples where

import Algebra.Structures.Coherent
import Algebra.Matrix
import Algebra.MPoly
import Algebra.Monomial
import Algebra.Ideals
import Algebra.Q

m :: Matrix (MPoly Q GrLex)
m = matrix [[1,2,3],[4,5,6],[7,8,9]]

v = matrix [[x],[y],[z]]

{- Coherence example:

This solves the system:

x*t1 + y^2*t2 + (zy-x^2)*t3 = 0

exCoherent = solveMxN (matrix [[x,y^2,(z*y-x^2)],[x,0,0]])

-}
-- Introduce some variables for testing:
x,y,z :: MPoly Q Lex
x = toMPoly [(1,[1])]
y = toMPoly [(1,[0,1])]
z = toMPoly [(1,[0,0,1])]

i,j :: Ideal (MPoly Q Lex)
i = Id [x+y,x]

j = gb i
{- Some tests:

-- Example from page 59 of Cox, with order x > y > z
f1 :: MPoly Q Lex
f1 = toMPoly [(4,[1,2,1]),(4,[0,0,2]),(-5,[3,0,0]),(7,[2,0,2])]
f2 :: MPoly Q GrLex
f2 = toMPoly [(4,[1,2,1]),(4,[0,0,2]),(-5,[3,0,0]),(7,[2,0,2])]
f3 :: MPoly Q GRevLex
f3 = toMPoly [(4,[1,2,1]),(4,[0,0,2]),(-5,[3,0,0]),(7,[2,0,2])]

f'  = x^2*y + x*y^2 + y^2
f1' = x*y - 1
f2' = y^2 - 1
test' = divide f' [f1',f2']
-}


-- Intersection test: 
-- ex1  = int (Id [x^2*y]) (Id [x*y^2])
-- ex1' = isIntersection int (Id [x^2*y]) (Id [x*y^2])

-- Some example ideals, for this to work x, y and z have to be defined with the correct type:
-- i1, i2, i3 :: Ideal (MPoly Q GrLex)
i1 = Id [ x^3-2*x*y, x^2*y-2*y^2+x ]
i2 = Id [ x*y+1, x^2+x ]
i3 = Id [ x*z-y^2, x^3-z^2 ]
f  = -4*x^2*y^2*z^2+y^6+3*z^5




{-
x,y,z :: MPoly Q Lex
x = toMPoly [(1,[1])]
y = toMPoly [(1,[0,1])]
z = toMPoly [(1,[0,0,1])]
-}
-- Example from page 59 of Cox, with order x > y > z
{-
f1 :: MPoly Q Lex
f1 = toMPoly [(4,[1,2,1]),(4,[0,0,2]),(-5,[3,0,0]),(7,[2,0,2])]
f2 :: MPoly Q GrLex
f2 = toMPoly [(4,[1,2,1]),(4,[0,0,2]),(-5,[3,0,0]),(7,[2,0,2])]
f3 :: MPoly Q GRevLex
f3 = toMPoly [(4,[1,2,1]),(4,[0,0,2]),(-5,[3,0,0]),(7,[2,0,2])]

f'  = x^2*y + x*y^2 + y^2
f1' = x*y - 1
f2' = y^2 - 1
test = divide f' [f1',f2']
-}
