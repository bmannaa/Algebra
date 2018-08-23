module Algebra.Structures.Rings where

import Test.QuickCheck
import Prelude hiding ((^^))


-------------------------------------------------------------------------------
-- | Rings
-- 
class Ring a where
  (<+>) :: a -> a -> a
  (<*>) :: a -> a -> a
  zero  :: a
  one   :: a
  neg   :: a -> a

--power
(^^) :: Ring a => a -> Int -> a
a^^i | i==0 = one
    | otherwise = a <*> a^^(i-1)
-- Subtraction:
(<->) :: Ring a => a -> a -> a
a <-> b = a <+> neg b

-- Division:
(</>) :: Field a => a -> a -> a
a </> b = a <*> inv b

-- Summation:
sumRing :: Ring a => [a] -> a
sumRing = foldr (<+>) zero

-- Exponentiation
(<^>) :: Ring a => a -> Integer -> a
x <^> 0 = one
x <^> y = if y < 0 
             then error "<^>: Input should be positive"
             else x <*> x <^> (y-1)

infixl 8 <^>
infixl 7 <*>
infixl 7 </>
infixl 6 <+>
infixl 6 <->

-- Addition satisfy the same properties as a commutative group
propAddAssoc :: (Eq a, Ring a) => a -> a -> a -> Bool
propAddAssoc a b c = (a <+> b) <+> c == a <+> (b <+> c)

propId :: (Eq a, Ring a) => a -> Property
propId a = a <+> zero == a .&. zero <+> a == a

propInv :: (Eq a, Ring a) => a -> Property
propInv a = neg a <+> a == zero .&. a <+> neg a == zero

propAddComm :: (Eq a, Ring a) => a -> a -> Bool
propAddComm x y = x <+> y == y <+> x

-- Multiplication is associative
propMulAssoc :: (Eq a, Ring a) => a -> a -> a -> Bool
propMulAssoc a b c = (a <*> b) <*> c == a <*> (b <*> c)

-- Multiplication is distributive over addition.
propRightDist :: (Eq a, Ring a) => a -> a -> a -> Bool
propRightDist a b c = (a <+> b) <*> c == (a <*> c) <+> (b <*> c)

propLeftDist :: (Eq a, Ring a) => a -> a -> a -> Bool
propLeftDist a b c = a <*> (b <+> c) == (a <*> b) <+> (a <*> c)

propUnit :: (Ring a, Eq a) => a -> Bool
propUnit a = one <*> a == a && a <*> one == a

propRing :: (Eq a, Ring a) => a -> a -> a -> Property
propRing a b c = propAddAssoc a b c .&. propId a            .&. 
                 propInv a          .&. propAddComm a b     .&. 
                 propMulAssoc a b c .&. propRightDist a b c .&. 
                 propLeftDist a b c .&. propUnit a


-------------------------------------------------------------------------------
-- | Commutative rings
--
class Ring a => CommutativeRing a where

propMulComm :: (Eq a, CommutativeRing a) => a -> a -> Bool
propMulComm a b = a <*> b == b <*> a

propCommRing :: (Eq a, CommutativeRing a) => a -> a -> a -> Property
propCommRing a b c = propRing a b c .&. propMulComm a b


-------------------------------------------------------------------------------
-- | Integral domains
--
class CommutativeRing a => IntegralDomain a where

-- An integral domain is a ring in which there are no zero divisors.
propZero :: (IntegralDomain a, Eq a) => a -> a -> a -> Bool
propZero a b c = if a <*> b == zero then a == zero || b == zero else True

propIntegralDomain :: (IntegralDomain a, Eq a) => a -> a -> a -> Property
propIntegralDomain a b c = propCommRing a b c .&. propZero a b c


-------------------------------------------------------------------------------
-- | Fields
--
class IntegralDomain a => Field a where
  inv :: a -> a

propMulInv :: (Field a, Eq a) => a -> Property
propMulInv a = a /= zero ==> inv a <*> a == one

propField :: (Field a, Eq a) => a -> a -> a -> Property
propField a b c = propMulInv a .&. propIntegralDomain a b c

---------------------------------------------------------------------------------
-- | Boolean ring

Class CommutativeRing a => BolleanRing a where
