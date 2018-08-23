module Algebra.PLM where

import Algebra.Structures.Rings
import Algebra.Ideals
import Algebra.Matrix

{-
Principal Localization Matrix for an ideal (x1,...,xn) is a matrix such that:

  o The sum of the diagonal should equal 1.
  o For all i, j, l in {1..n}: a_lj * x_i = a_li * x_j

-}
propPLM :: (CommutativeRing a, Eq a) => Ideal a -> Matrix a -> Bool
propPLM (Id xs) (M vs) 
  | isSquareMatrix (M vs) = 
    let as      = map unVec vs
        sumDiag = sumRing [ ai !! i | (ai,i) <- zip as [0..]]
        n       = length as - 1
        ijl     = and [ as !! l !! j <*> xs !! i == 
                        as !! l !! i <*> xs !! j
                      | i <- [0..n]
                      , j <- [0..n]
                      , l <- [0..n]
                      ]
    in one == sumDiag && ijl
  | otherwise = error "isPLM: Not square matrix"

-- Maybe it would be nice to add some of the properties in Proposition 2.6 in:
-- http://hlombardi.free.fr/liens/salouThesis.pdf
