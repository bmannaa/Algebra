{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}
module Algebra.NonMonadicHenselLemma where
import Algebra.FormalPowerSeries
import Algebra.UPoly
--import Test.QuickCheck
import Algebra.Structures.Rings
import Algebra.Structures.EuclideanDomains 
import Algebra.Q
import Algebra.TypeString.Char hiding (Q,F,E)
import Data.Stream as St
import Data.List as Lst
import Prelude hiding (map,repeat,zipWith)


--useful helpers
hd (PS bs) = St.head bs
tl (PS bs) = PS $ St.tail bs
(PS bs) !!! n = bs St.!! n

-- | the type of polynomials with power series coeff
type F a x y = UPoly (PSeries a x) y 
-- | the type of power series with polynomial coeff
type E a y x = PSeries (UPoly a y) x
--test case
b0X :: PSeries Q X_
b0X = one
b1X :: PSeries Q X_
b1X = PS $ ll[-1,-1]
fXY2 :: F Q X_ Y_
fXY2 = UP [b1X,zero,zero,zero,one]
f2Y1 :: UPoly Q Y_
f2Y1 = UP [-1,0,1]
f2Y2 :: UPoly Q Y_
f2Y2 = UP [1,0,1]
--test case
a_2X :: PSeries Q X_
a_2X = one
a_1X :: PSeries Q X_
a_1X = PS $ ll[-4, -2]
a_0X :: PSeries Q X_
a_0X = PS $ ll[3,6]
fXY :: F Q X_ Y_
fXY = UP [a_0X, a_1X, a_2X]

-- | the degree of a polynomial with power series coeff
ydeg :: (CommutativeRing a) => F a x y -> Int
ydeg (UP as) | length as > 0 = length as - 1
             | otherwise     = 0
-- | test if a polynomials is monic (should be moved to UPoly)
monic :: (IntegralDomain a, Eq a) => F a x y -> Bool
monic (UP as) = last as == one

-- | coprimality test for polynomials (shall be moved to UPoly)
--coprime :: (Field a, Eq a) => UPoly a y -> UPoly a y -> Bool
--coprime fX gX = (d $ euclidAlg fX gX) < 1
--test case
fY1 :: UPoly Q Y_
fY1 = UP $ [-1,1]
fY2 :: UPoly Q Y_
fY2 = UP $ [-3,1]

-- | the Y projection of a polynomial F(X,Y). i.e. F(0,Y)
proj_y :: (CommutativeRing a) => F a x y -> UPoly a y
proj_y (UP as) = UP $ Lst.map hd as

-- | the cannonical embedding (injective homomorphism) :  k[[X]][Y] -> k[Y][[X]]
phi :: (CommutativeRing a, Eq a) => F a x y -> E a y x
phi f = PS $ phi' 0 f

phi' :: (CommutativeRing a, Eq a) => Int -> F a x y -> Stream (UPoly a y)
phi' n p@(UP as) = (toUPoly $ Lst.map (\c -> c !!! n) as) <:> (phi' (n+1) p)
 
-- | a homomorphism  (f : k[Y][[X]] and f bounded in Y) -> k [[X]] [Y].
-- generally the map k[Y][[X]] -> k [[X]] [Y] is not injective. but the partial map defined here is indeed injective
-- since any f in k[Y] [[X]] bounded in Y is equal to one in k [[X]][Y]
--and back
--the map is not surjective so this is not logically precise
--but since we pass the y_degree this should work fine
psi :: (CommutativeRing a, Eq a) => Int -> E a y x -> F a x y
psi deg p = UP $ psi' deg p 0

psi' :: (CommutativeRing a, Eq a) => Int -> E a y x -> Int -> [PSeries a x]
psi' deg p@(PS bs) n | n > deg   = []
                     | otherwise = (PS $ St.map (\x -> x ! n) bs) : psi' deg p (n+1)
                     where (UP as) ! n | n > length as - 1 = zero
                                       | otherwise = as Lst.!! n 

--the lemma
lemma :: (CommutativeRing a, Eq a) => F a x y -> UPoly a y -> UPoly a y -> UPoly a y -> UPoly a y-> (F a x y, F a x y)
lemma fXY g_0 h_0 h' g' = (psi (fromInteger $ deg g_0) gYX, psi (fromInteger $ deg h_0) hYX)
                  where 
                      f' = phi fXY --k[y][[x]]
                      u  = (hd $ tl f') <:> fromPS ((tl $ tl f') <-> (tl gYX <*> tl hYX))
                      _h = St.map (h' <*>) u
                      _g = St.map (g' <*>) u
                      hYX = PS $ h_0 <:> St.map (\x -> snd $ euclid x h_0) _h
                      e = St.map (\x -> fst $ euclid x h_0) _h
                      gYX = PS $ g_0 <:> (fromPS $ PS _g <+> (PS $ St.map (g_0 <*>) e))
                      y_d = ydeg fXY

