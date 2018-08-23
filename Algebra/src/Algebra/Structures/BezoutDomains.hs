{-# LANGUAGE FlexibleInstances, UndecidableInstances, OverlappingInstances #-}
module Algebra.Structures.BezoutDomains where

import Test.QuickCheck 

import Algebra.Structures.Rings
import Algebra.Structures.Coherent
import Algebra.Structures.EuclideanDomains
import Algebra.Structures.PruferDomains
import Algebra.Structures.StronglyDiscrete
import Algebra.PLM
import Algebra.Matrix
import Algebra.Ideals


-------------------------------------------------------------------------------
-- | Bézout domains
-- 
-- Compute a principal ideal from another ideal. Also give witness that the
-- principal ideal is equal to the first ideal.
--
-- <a1,...,an> = (<a>,ui,vi)
-- sum (ui * ai) = a
-- ai = vi * a
--
class IntegralDomain a => BezoutDomain a where
  toPrincipal :: Ideal a -> (Ideal a,[a],[a])

propToPrincipal :: (BezoutDomain a, Eq a) => Ideal a -> Bool
propToPrincipal = isPrincipal . (\(a,_,_) -> a) . toPrincipal

propIsSameIdeal :: (BezoutDomain a, Eq a) => Ideal a -> Bool
propIsSameIdeal (Id as) =
  let (Id [a], us, vs) = toPrincipal (Id as) 
  in a == foldr1 (<+>) (zipWith (<*>) as us) 
  && and [ ai == a <*> vi | (ai,vi) <- zip as vs ]
  && length us == l_as && length vs == l_as
  where l_as = length as

propBezoutDomain :: (BezoutDomain a, Eq a) => Ideal a -> a -> a -> a -> Property
propBezoutDomain id@(Id xs) a b c = zero `notElem` xs ==> 
  propToPrincipal id .&. propIsSameIdeal id .&. propIntegralDomain a b c 


-------------------------------------------------------------------------------
-- | Euclidean domain -> Bézout domain
-- 
instance (EuclideanDomain a, Eq a) => BezoutDomain a where
  toPrincipal (Id [x]) = (Id [x], [one], [one])
  toPrincipal (Id xs)  = (Id [a], as, [ quotient ai a | ai <- xs ])
    where
    a  = genEuclidAlg xs
    as = genExtEuclidAlg xs


-------------------------------------------------------------------------------
-- | Intersection of ideals 
-- 
-- If one of the ideals is the zero ideal then the intersection 
-- is the zero ideal.
-- If one of the ideals contain zeroes this is handled specially.
-- 
intersectionB :: (BezoutDomain a, Eq a) 
              => Ideal a 
              -> Ideal a 
              -> (Ideal a, [[a]], [[a]])
intersectionB (Id xs) (Id ys) 
  | xs' == [] = zeroIdealWitnesses xs ys
  | ys' == [] = zeroIdealWitnesses xs ys
  | otherwise = (Id [l], [handleZero xs as], [handleZero ys bs])
  where
  xs'            = filter (/= zero) xs
  ys'            = filter (/= zero) ys

  (Id [a],us1,vs1) = toPrincipal (Id xs') 
  (Id [b],us2,vs2) = toPrincipal (Id ys')

  (Id [g],[u1,u2],[v1,v2]) = toPrincipal (Id [a,b])

  l  = g <*> v1 <*> v2
  as = map (v2 <*>) us1
  bs = map (v1 <*>) us2
  
  -- Handle the zeroes specially. If the first element in xs is a zero
  -- then the witness should be zero otherwise use the computed witness. 
  handleZero xs [] 
    | all (==zero) xs = xs
    | otherwise       = error "intersectionB: This should be impossible"
  handleZero (x:xs) (a:as) 
    | x == zero = zero : handleZero xs (a:as)
    | otherwise = a    : handleZero xs as
  handleZero [] _  = error "intersectionB: This should be impossible"


-------------------------------------------------------------------------------
-- | Coherence
-- 
solveB :: (BezoutDomain a, Eq a) => Vector a -> Matrix a
solveB x = solveWithIntersection x intersectionB

-- instance (BezoutDomain r, Eq r) => Coherent r where
--   solve x = solveWithIntersection x intersectionB


-------------------------------------------------------------------------------
-- | Principal localization matrix
--
computePLM_B :: (BezoutDomain a, Eq a) => Ideal a -> Matrix a
computePLM_B (Id xs) = 
  let (Id [g],us,ys) = toPrincipal (Id xs)
      n              = length xs - 1
  in M [ Vec [ us !! i <*> ys !! j | j <- [0..n] ] | i <- [0..n] ]


-------------------------------------------------------------------------------
-- | Strongly discreteness for Euclidean domains
-- 
-- Given x, compute as such that x = sum (a_i * x_i)
--
instance (EuclideanDomain a, Eq a) => StronglyDiscrete a where
  member x (Id xs) = if r == zero then Just witness else Nothing
    where
    -- (<g>, as, bs)   = <x1,...,xn>
    -- sum (a_i * x_i) = g
    -- x_i             = b_i * g
    (Id [g], as, bs) = toPrincipal (Id xs)

    -- x = qg + r
    -- If r = 0 then x is a member of xs
    (q,r)   = quotientRemainder x g
    
    -- x = qg = q (sum (ai * xi)) = sum (q * ai * xi)
    witness = map (q <*>) as

-------------------------------------------------------------------------------
-- | Bezout domain -> Prüfer domain
--
{-
Prufer: forall a b exists u v w t.  u+t = 1 &  ua = vb & wa = tb

We consider only domain.
We assume we have the Bezout condition: given a, b we can find g,a1,b1,c,d s.t.

a = g a1
b = g b1
1 = c a1 + d b1

We try then 

u = d b1
t = c a1

We should find v such that
a d b1 = b v
this simplifies to 
g a1 d b1 = g b1 v
and we can take 
v = a1 d
Similarly we can take 
w = b1 c

We have shown that Bezout domain -> Prufer domain.
-}
instance (BezoutDomain a, Eq a) => PruferDomain a where
  calcUVW a b | a == zero = (one,zero,zero)
              | b == zero = (zero,zero,zero)
              | otherwise = fromUVWTtoUVW (u,v,w,t)
    where
    -- Compute g, a1 and b1 such that:
    -- a = g*a1
    -- b = g*b1
    (g,[_,_],[a1,b1])  = toPrincipal (Id [a,b])
    
    -- Compute c and d such that:
    -- 1 = a1*c + a2*d
    (_,[c,d],_) = toPrincipal (Id [a1,b1])

    u = d <*> b1
    t = c <*> a1
    v = d <*> a1
    w = c <*> b1
