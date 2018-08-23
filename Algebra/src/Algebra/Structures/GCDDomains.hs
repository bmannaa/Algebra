{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
module Algebra.Structures.GCDDomains where

import Test.QuickCheck

import Algebra.Structures.Rings
import Algebra.Structures.BezoutDomains
import Algebra.Ideals

class IntegralDomain a => GCDDomain a where
  -- Compute gcd(a,b) = (g,x,y) such that g = gcd(a,b) and
  --   a = gx
  --   b = gy
  -- and a, b /= 0
  gcd' :: a -> a -> (a,a,a)

propGCD :: (GCDDomain a, Eq a) => a -> a -> Property
propGCD a b = a /= zero && b /= zero ==> a == g <*> x && b == g <*> y
  where
  (g,x,y) = gcd' a b

propGCDDomain :: (Eq a, GCDDomain a, Arbitrary a, Show a) => a -> a -> a -> Property
propGCDDomain a b c = propIntegralDomain a b c .&. propGCD a

-- This can be used to compute gcd of a list of non-zero elements
-- genGCD :: ?
-- genGCD = ?

instance BezoutDomain a => GCDDomain a where
  gcd' a b = (g,x,y)
    where
    (Id [g],_,[x,y]) = toPrincipal (Id [a,b])
