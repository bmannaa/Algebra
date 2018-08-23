{-# LANGUAGE TypeSynonymInstances #-}
module Algebra.Z where

import Test.QuickCheck

import qualified Algebra.Structures.Groups as G
import Algebra.Structures.Rings
import Algebra.Structures.PruferDomains
import Algebra.Structures.BezoutDomains
import Algebra.Structures.EuclideanDomains
import Algebra.Ideals

type Z = Integer

instance G.Group Z where
  zero  = 0
  (<+>) = (+)
  neg   = negate
  
instance G.AbelianGroup Z where

instance Ring Z where
  (<+>) = (+)
  zero  = 0
  one   = 1
  neg   = negate
  (<*>) = (*)

instance CommutativeRing Z where

instance IntegralDomain Z where

instance EuclideanDomain Z where
  d = abs
  quotientRemainder = quotRem
