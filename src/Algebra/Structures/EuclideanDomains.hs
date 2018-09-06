{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
module Algebra.Structures.EuclideanDomains where

import Test.QuickCheck

import Algebra.Structures.Rings
import Algebra.Structures.Coherent
import Algebra.Ideals


-------------------------------------------------------------------------------
-- | Euclidean domains
--
-- Given a and b compute (q,r) such that a = bq + r and r = 0 || d r < d b 
--
class IntegralDomain a => EuclideanDomain a where
  d :: a -> Integer
  quotientRemainder :: a -> a -> (a,a)

-- Check both that |a| <= |ab| and |a| >= 0 for all a,b
propD :: (EuclideanDomain a, Eq a) => a -> a -> Property
propD a b = a /= zero && b /= zero ==>
  d a <= d (a <*> b) && d a >= 0 && d b >= 0

propQuotRem :: (EuclideanDomain a, Eq a) => a -> a -> Property
propQuotRem a b = b /= zero ==> 
  let (q,r) = quotientRemainder a b 
  in a == b <*> q <+> r && (r == zero || d r < d b)

propEuclideanDomain :: (EuclideanDomain a, Eq a) => a -> a -> a -> Property
propEuclideanDomain a b c = a /= zero && b /= zero && c /= zero ==>  
  propD a b .&. propQuotRem a b .&. propIntegralDomain a b c


-------------------------------------------------------------------------------
-- Operations
--
modulo :: EuclideanDomain a => a -> a -> a
modulo a b = snd (quotientRemainder a b)

quotient :: EuclideanDomain a => a -> a -> a
quotient a b = fst (quotientRemainder a b)

divides :: (EuclideanDomain a, Eq a) => a -> a -> Bool
divides a b = modulo b a == zero

-- The Euclidean algorithm for calculating the GCD of a and b
euclidAlg :: (EuclideanDomain a, Eq a) => a -> a -> a
euclidAlg a b | a == zero && b == zero = error "GCD of 0 and 0 is undefined"
              | b == zero = a
              | otherwise = euclidAlg b (a `modulo` b)

genEuclidAlg :: (EuclideanDomain a, Eq a) => [a] -> a
genEuclidAlg = foldl euclidAlg zero

-- Lowest common multiple, (a*b)/gcd(a,b)
lcmE :: (EuclideanDomain a, Eq a) => a -> a -> a
lcmE a b = quotient (a <*> b) (euclidAlg a b)

genLcmE :: (EuclideanDomain a, Eq a) => [a] -> a
genLcmE xs = quotient (foldr1 (<*>) xs) (genEuclidAlg xs)

-- The extended Euclidean algorithm. 
-- Computes x and y in ax + by = gcd(a,b)
extendedEuclidAlg :: (EuclideanDomain a, Eq a) => a -> a -> (a,a)
extendedEuclidAlg a b | modulo a b == zero = (zero,one)
                      | otherwise = let (x,y) = extendedEuclidAlg b (a `modulo` b)
                                    in (y, x <-> y <*> (a `quotient` b))

propExtendedEuclidAlg :: (EuclideanDomain a, Eq a) => a -> a -> Property
propExtendedEuclidAlg a b = a /= zero && b /= zero ==> 
  let (x,y) = extendedEuclidAlg a b in a <*> x <+> b <*> y == euclidAlg a b

-- Generalised extended Euclidean algorithm
-- Solves: a_1 x_1 + ... + a_n x_n = gcd (a_1,...,a_n)
genExtEuclidAlg :: (EuclideanDomain a, Eq a) => [a] -> [a]
genExtEuclidAlg [x,y] = let (a,b) = extendedEuclidAlg x y in [a,b]
genExtEuclidAlg xs    =
  let (x,y) = extendedEuclidAlg (genEuclidAlg (init xs)) (last xs)
  in map (x<*>) (genExtEuclidAlg (init xs)) ++ [y]

propGenExtEuclidAlg :: (EuclideanDomain a, Eq a) => [a] -> Property
propGenExtEuclidAlg xs = all (/= zero) xs && length xs >= 2 ==> 
  foldr (<+>) zero (zipWith (<*>) (genExtEuclidAlg xs) xs) == genEuclidAlg xs
