{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Algebra.ZSqrt5 where

import Test.QuickCheck

import Algebra.Structures.Rings
import Algebra.Structures.EuclideanDomains
import Algebra.Structures.BezoutDomains
import Algebra.Structures.PruferDomains
import Algebra.Structures.Coherent
import Algebra.Ideals
import Algebra.Z
import Algebra.Q

-- Model Z[sqrt(-5)] as a pair such that (a,b) = a + b*sqrt(-5)
newtype ZSqrt5 = ZSqrt5 (Z,Z)
  deriving (Eq,Ord,Arbitrary)

instance Show ZSqrt5 where
  show (ZSqrt5 (a,b)) = show a ++ " + " ++ show b ++ " * sqrt(-5)"

-- Arithmetical properties
instance Ring ZSqrt5 where
  (ZSqrt5 (a,b)) <+> (ZSqrt5 (c,d)) = ZSqrt5 (a + c, b + d)
  (ZSqrt5 (a,b)) <*> (ZSqrt5 (c,d)) = ZSqrt5 (a*c - 5*b*d, a*d + b*c)
  neg (ZSqrt5 (a,b))                = ZSqrt5 (neg a, neg b)
  zero                              = ZSqrt5 (0,0)
  one                               = ZSqrt5 (1,0)
  
instance CommutativeRing ZSqrt5 where

instance IntegralDomain ZSqrt5 where

propIntDomZSqrt5 :: ZSqrt5 -> ZSqrt5 -> ZSqrt5 -> Property
propIntDomZSqrt5 = propIntegralDomain

--------------------------------------------------------------------------------
-- Useful auxiliary functions:

(*>), (+>) :: Z -> ZSqrt5 -> ZSqrt5
r *> (ZSqrt5 (a,b)) = ZSqrt5 (r*a,r*b)
r +> (ZSqrt5 (a,b)) = ZSqrt5 (r+a,b)

(<*), (<+) :: ZSqrt5 -> Z -> ZSqrt5
(ZSqrt5 (a,b)) <* r = ZSqrt5 (a*r,b*r)
(ZSqrt5 (a,b)) <+ r = ZSqrt5 (a+r,b)

infixl 7 *>, <*
infixl 6 +>, <+

--------------------------------------------------------------------------------

instance PruferDomain ZSqrt5 where
  -- Assume /= 0
  calcUVW (ZSqrt5 (a,b)) (ZSqrt5 (c,d)) = (u,v,w) 
    where
    -- s = (p,q)
    s :: (Q,Q) 
    s = ( toQ (a * c + 5 * b * d) / toQ (c^2 + 5 * d^2)
        , toQ (b * c - a * d) / toQ (c^2 + 5 * d^2))
    
    -- a0's^2 + a1's + a2' = 0
    a0' = c^2 + 5 * d^2
    a1' = -2 * (a * c + 5 * b * d)
    a2' = a^2 + 5 * b^2

    -- Make <a0,a1,a2> = 1
    g  = genEuclidAlg [a0',a1',a2']
    a0 = a0' `quotient` g
    a1 = a1' `quotient` g
    a2 = a2' `quotient` g

    -- n0 * a0 + n1 * a1 + n2 * a2 = 1
    (Id [1],[n0,n1,n2],_) = toPrincipal (Id [a0,a1,a2])

    a0s    = case s of
      (p,q) -> ZSqrt5 (toZ (a0' <*> p), toZ (a0' <*> q))
      where a0' = toQ a0
    a0sa1  = a0s <+ a1
    a0sa1s = ZSqrt5 (-a2,0)

    alpha = a0s 
    beta  = a0sa1s

    m0 = n0
    m1 = -n1
    m2 = n1
    m3 = -n2

    u = m0 * a0 +> m2 *> a0sa1
    v = m0 *> alpha <+> m2 *> beta
    w = m1 * a0 +> m3 *> a0sa1

propPruferDomZSqrt5 :: ZSqrt5 -> ZSqrt5 -> ZSqrt5 -> Property
propPruferDomZSqrt5 x@(ZSqrt5 (a,b)) y@(ZSqrt5 (c,d)) z@(ZSqrt5 (e,f)) = 
  a /= 0 && b /= 0 && c /= 0 && d /= 0 && e /= 0 && f /= 0 ==> propPruferDomain x y z

instance Coherent ZSqrt5 where
  solve = solvePD

--------------------------------------------------------------------------------

x' = Id [ZSqrt5 (2,0)]
y' = Id [ZSqrt5 (1,-1)]

-- <-6 + 0 * sqrt(-5),4 + 2 * sqrt(-5)> =
-- <-6, 4+2y> =
-- <-4,2+y>

-- (1-y)(2,1+y) = <2-2y,1-y^2> = <2-2y,1-(-5)> = <2-2y,6>
