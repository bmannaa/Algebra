module Algebra.Structures.FieldOfFractions where

import Test.QuickCheck

import Algebra.Structures.Rings
import Algebra.Structures.GCDDomains


-------------------------------------------------------------------------------
-- | Field of fractions
-- 
-- The field of fractions over a GCD domain. The reason that it is an GCD 
-- domain is that we only want to work over reduced quotients.
--
newtype  CommutativeRing a => FieldOfFractions a = F (a,a)

instance (CommutativeRing a, Show a, Eq a) => Show (FieldOfFractions a) where
  show (F (a,b)) | b == one  = show a
                 | otherwise = case show b of
                    ('-':xs) -> "-" ++ "(" ++ show a ++ ")" ++ "/" ++ "(" ++ xs ++ ")"
                    xs -> "(" ++ show a ++ ")" ++ "/" ++ "(" ++ xs ++ ")"

instance (CommutativeRing a, Eq a, Arbitrary a) => Arbitrary (FieldOfFractions a) where
  arbitrary = do
    a <- arbitrary
    b <- arbitrary
    if b == zero 
       then return $ F (a,one)
       else return $ F (a,b)


-- Embed a value in the field of fractions
toFieldOfFractions :: CommutativeRing a => a -> FieldOfFractions a
toFieldOfFractions a = F (a,one)

fromFieldOfFractions :: (CommutativeRing a, Eq a) => FieldOfFractions a -> a
fromFieldOfFractions (F (a,b)) 
  | b == one  = a
  | otherwise = error "FieldOfFractions: Can't extract value"

-- Reduce an element
reduce :: (GCDDomain a, Eq a) => FieldOfFractions a -> FieldOfFractions a
reduce (F (a,b)) | b == zero = error "FieldOfFractions: Division by zero"
                 | a == zero = F (zero,one)
                 | otherwise = if g == one
                                  then F (a,b)
                                  else F (x,y)
  where
  (g,x,y) = gcd' a b

propReduce :: (GCDDomain a, Eq a) => FieldOfFractions a -> Property
propReduce f@(F (a,b)) = a /= zero && b /= zero ==> g == one
  where
  F (c,d) = reduce f
  (g,_,_) = gcd' c d

instance (GCDDomain a, Eq a) => Eq (FieldOfFractions a) where
  f == g = a <*> d == b <*> c
    where
    F (a,b) =  f
    F (c,d) =  g

instance (CommutativeRing a, Eq a) => Ring (FieldOfFractions a) where
  (F (a,b)) <+> (F (c,d)) = (F (a <*> d <+> c <*> b,b <*> d))
  (F (a,b)) <*> (F (c,d)) = (F (a <*> c,b <*> d))
  neg (F (a,b))           = (F (neg a,b))
  one                     = toFieldOfFractions one
  zero                    = toFieldOfFractions zero

instance (CommutativeRing a, Eq a) => CommutativeRing (FieldOfFractions a) where
instance (CommutativeRing a, Eq a) => IntegralDomain (FieldOfFractions a) where

-- Compute the inverse of an element
inverse :: (CommutativeRing a, Eq a) => FieldOfFractions a -> FieldOfFractions a 
inverse (F (a,b)) | b /= zero && a /= zero = F (b,a)
                  | otherwise = error "FieldOfFraction: Division by zero"

instance (CommutativeRing a, Eq a) => Field (FieldOfFractions a) where
  inv = inverse
