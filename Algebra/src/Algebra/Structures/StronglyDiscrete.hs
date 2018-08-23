module Algebra.Structures.StronglyDiscrete where

import Algebra.Structures.Rings
import Algebra.Ideals


-------------------------------------------------------------------------------
-- | Strongly discrete rings
--
-- A ring is called strongly discrete if ideal membership is decidable.
-- Nothing correspond to that x is not in the ideal and Just is the witness.
-- Examples include all euclidean domains and the polynomial ring.
--
class Ring a => StronglyDiscrete a where
  member :: a -> Ideal a -> Maybe [a]

-- Test that the witness is actually a witness.
propStronglyDiscrete :: (CommutativeRing a, StronglyDiscrete a, Eq a)
                     => a -> Ideal a -> Bool                  
propStronglyDiscrete x id@(Id xs) = case member x id of
  Just as -> x == sumRing (zipWith (<*>) xs as) && length xs == length as
  Nothing -> True
