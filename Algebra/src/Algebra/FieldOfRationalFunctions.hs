{-# LANGUAGE TypeSynonymInstances #-}
module Algebra.FieldOfRationalFunctions where

import Test.QuickCheck

import Algebra.Structures.Rings
import Algebra.Structures.FieldOfFractions
import Algebra.UPoly
import Algebra.Q
import Algebra.TypeString.Char (X_)


-------------------------------------------------------------------------------
-- | Field of rational functions
--
-- The field of rational functions for a polynomial ring k[x] is the field of
-- fractions for it and it is denoted by k(x). 
--
type FieldOfRationalFunctions k x = FieldOfFractions (UPoly k x)

type QX = FieldOfRationalFunctions Q X_

toQX :: Qx -> QX
toQX = toFieldOfFractions

toQx :: QX -> Qx
toQx = fromFieldOfFractions

propFieldQX :: QX -> QX -> QX -> Property
propFieldQX = propField

-- | k(x) Num.
instance (Show k, Field k, Num k, Show x) => Num (FieldOfRationalFunctions k x) where
  (+)    = (<+>)
  (-)    = (<->)
  (*)    = (<*>)
  fromInteger x = toFieldOfFractions $ UP [fromInteger x]
