{-# LANGUAGE TypeSynonymInstances #-}
module Algebra.Q where

import Test.QuickCheck
import qualified Math.Algebra.Field.Base as A (Q(..)) 
import Data.Ratio 

import qualified Algebra.Structures.Groups as G
import Algebra.Structures.Rings
import Algebra.Z

type Q = A.Q

instance G.Group Q where
  zero  = 0
  (<+>) = (+)
  neg   = negate

instance G.AbelianGroup Q where

instance Ring Q where
  (<+>) = (+)
  (<*>) = (*)
  zero  = 0
  one   = 1
  neg   = negate

instance CommutativeRing Q where

instance IntegralDomain Q where

instance Field Q where
  inv x = 1/x

instance Arbitrary Q where
  arbitrary = do x <- arbitrary
                 y <- arbitrary
                 if y == 0 
                    then return $ A.Q $ x % 1
                    else return $ A.Q $ x % y

toQ :: Z -> Q
toQ = fromInteger

toZ :: Q -> Z
toZ (A.Q x) | denominator x == 1 = numerator x
            | otherwise          = error "toZ: The denominator must be 1"

{-
import Algebra.Structures.Rings
import Algebra.Structures.FieldOfFractions
import Algebra.Z

type Q = FieldOfFractions Z

instance Num Q where
  (+)              = (<+>)
  (*)              = (<*>)
  abs (F (a,b))    = F (abs a, b) 
  signum (F (a,_)) = F (signum a,one)
  fromInteger      = toQ

instance Fractional Q where
  (/) = (</>)
  fromRational = undefined
--   fromRational (a :% b) = reduce $ F (a,b)

toQ :: Z -> Q
toQ = toFieldOfFractions

toZ :: Q -> Z
toZ = fromFieldOfFractions
-}    
