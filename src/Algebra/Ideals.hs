module Algebra.Ideals where

import Algebra.Structures.Rings

import Data.List (intersperse,nub)
import Test.QuickCheck

-- Finitely generated ideals in commutative rings.
data CommutativeRing a => Ideal a = Id [a]

instance (CommutativeRing a, Show a) => Show (Ideal a) where
  show (Id xs) = "<" ++ concat (intersperse "," (map show xs)) ++ ">"

instance (Eq a, IntegralDomain a, Arbitrary a) => Arbitrary (Ideal a) where
  arbitrary = do xs' <- arbitrary
                 let xs = filter (/= zero) xs'
                 if xs == [] then return (Id [one]) else return (Id (nub xs))

zeroIdeal :: CommutativeRing a => Ideal a
zeroIdeal = Id [zero]

isPrincipal :: CommutativeRing a => Ideal a -> Bool
isPrincipal (Id xs) = length xs == 1

fromId :: CommutativeRing r => Ideal r -> [r]
fromId (Id xs) = xs

eval :: CommutativeRing a => a -> Ideal a -> a
eval x (Id xs) = foldr (<+>) zero (map (<*> x) xs)

-- Addition of ideals.
addId :: (Eq a, CommutativeRing a) => Ideal a -> Ideal a -> Ideal a
addId (Id xs) (Id ys) = Id (nub (xs ++ ys))

-- Multiplication of ideals.
-- Handle the zero ideal specially.
-- Id [ f <*> g | f <- xs, g <- ys ] <-- Naive implementation
mulId :: (Eq a, CommutativeRing a) => Ideal a -> Ideal a -> Ideal a
mulId (Id xs) (Id ys) = case filter (/= zero) (nub [ f <*> g | f <- xs, g <- ys ]) of
  [] -> zeroIdeal
  xs -> Id xs

{-
The operation should give a witness that the comuted ideal contains
the same elements.

I `op` J = K
[ x_1, ..., x_n ] `op` [ y_1, ..., y_m ] = [ z_1, ..., z_l ]
z_k = a_k1 * x_1 + ... + a_kn * x_n
    = b_k1 * y_1 + ... + b_km * y_m

-}
isSameIdeal :: (CommutativeRing a, Eq a) 
            => (Ideal a -> Ideal a -> (Ideal a, [[a]], [[a]]))
            -> Ideal a 
            -> Ideal a 
            -> Bool
isSameIdeal op (Id xs) (Id ys) = 
  let (Id zs, as, bs) = (Id xs) `op` (Id ys)
  in length as == length zs && length bs == length zs
     &&
     and [ z_k == sumRing (zipWith (<*>) a_k xs) && length a_k == length xs
         | (z_k,a_k) <- zip zs as ]
     &&
     and [ z_k == sumRing (zipWith (<*>) b_k ys) && length b_k == length ys
         | (z_k,b_k) <- zip zs bs ]

-- Compute witnesses for two lists for the zero ideal. This is used when 
-- computing the intersection of two ideals.
zeroIdealWitnesses :: (CommutativeRing a) => [a] -> [a] -> (Ideal a, [[a]], [[a]])
zeroIdealWitnesses xs ys = ( zeroIdeal
                           , [replicate (length xs) zero]
                           , [replicate (length ys) zero])
