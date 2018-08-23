{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
module Algebra.Structures.PruferDomains where

import Test.QuickCheck
import Data.List (nub)

import Algebra.Structures.Rings
import Algebra.Structures.Coherent
import Algebra.Ideals
import Algebra.Matrix


-------------------------------------------------------------------------------
-- | Prufer domain
--
class IntegralDomain a => PruferDomain a where
  --         a    b     u v w
  calcUVW :: a -> a -> (a,a,a)

-- Property specifying that:
-- au = bv and b(1-u) = aw
propCalcUVW :: (PruferDomain a, Eq a) => a -> a -> Property 
propCalcUVW a b = a <*> u == b <*> v .&. b <*> (one <-> u) == a <*> w
  where (u,v,w) = calcUVW a b

propPruferDomain :: (PruferDomain a, Eq a) => a -> a -> a -> Property
propPruferDomain a b c = propCalcUVW a b .&. propIntegralDomain a b c

{- Another characterization of Prüfer domains:
Given a and b, want to compute u, v, w, t such that:

ua  = vb
wa  = tb
u+t = 1

I can compute:

ax     = by
b(1-x) = az 

So if:

u = x
v = y
w = z
t = 1-x

I get:

u + t = x + 1 - x = 1
-}
calcUVWT :: PruferDomain a => a -> a -> (a,a,a,a)
calcUVWT a b = (x,y,z,one <-> x)
  where (x,y,z) = calcUVW a b

propCalcUVWT :: (PruferDomain a, Eq a) => a -> a -> Property
propCalcUVWT a b =  u <*> a == v <*> b 
                .&. w <*> a == t <*> b
                .&. u <+> t == one
  where (u,v,w,t) = calcUVWT a b

fromUVWTtoUVW :: PruferDomain a => (a,a,a,a) -> (a,a,a)
fromUVWTtoUVW (u,v,w,t) = (u,v,w) 

-------------------------------------------------------------------------------
-- | Coherence
--

-- Compute a principal localization matrix for an ideal in a Prufer domain
computePLM_PD :: (PruferDomain a, Eq a) => Ideal a -> Matrix a
computePLM_PD (Id [_])   = matrix [[one]]
computePLM_PD (Id [a,b]) = let (u,v,w,t) = calcUVWT b a 
                           in M [ Vec [u,v], Vec [w,t]]
computePLM_PD (Id xs)    = matrix a
  where
  -- Use induction hypothesis to construct a matrix for n-1:
  x_is = init xs
  b    = unMVec $ computePLM_PD (Id x_is)
  m    = length b - 1
  
  -- Let s_i be b_ii:
  s_is = [ (b !! i) !! i | i <- [0..m]]

  -- Take out x_n:
  x_n  = last xs

  -- Compute (u_i, v_i, w_i, t_i) for <x_n,x_i>:
  uvwt_i = [ calcUVWT x_n x_i | x_i <- x_is ]
    
  -- Take out all u, v, w, and t:
  u_is = [ u_i | (u_i,_,_,_) <- uvwt_i ]
  v_is = [ v_i | (_,v_i,_,_) <- uvwt_i ]
  w_js = [ w_i | (_,_,w_i,_) <- uvwt_i ]
  t_is = [ t_i | (_,_,_,t_i) <- uvwt_i ]
  
  -- COMPUTE a_ij for 1 <= i,j < n
  -- i = row
  -- j = column
  a_ij = [ [ if i == j 
                then (s_is !! i) <*> (u_is !! i)
                else (u_is !! i) <*> (b !! i !! j)
           | j <- [0..m] ]
         | i <- [0..m] ]

  -- COMPUTE a_nn
  a_nn = sumRing $ zipWith (<*>) s_is t_is

  -- COMPUTE a_ni for 1 <= i < n
  -- THIS IS THE LAST ROW
  a_ni = [ sumRing [ (b !! j !! i) <*> (w_js !! j)
                   | j <- [0..m] ]
         | i <- [0..m] ]

  -- COMPUTE a_in for 1 <= i < n
  -- THIS IS THE LAST COLUMN
  a_in = [ (s_is !! i) <*> (v_is !! i)
         | i <- [0..m] ]

  -- ASSEMBLE EVERYTHING
  a = [ x ++ [y] | (x,y) <- zip a_ij a_in ] ++ [a_ni ++ [a_nn]]


-- Ideal inversion. Gived I compute J such that IJ is principal.
-- Uses the principal localization matrix for the ideal.
invertIdeal :: (PruferDomain a, Eq a) => Ideal a -> Ideal a
invertIdeal xs = 
  let a = unMVec $ computePLM_PD xs

      -- Pick out the first column
      a_njs = [ head (a !! j) | j <- [0..length a - 1]]
  in Id a_njs

-- XXX: This is buggy at the moment... Witnesses is not correctly computed!
-- Compute the intersection of I and J by:
--       
--       (I ∩ J)(I + J) = IJ  => (I ∩ J)(I + J)(I + J)' = IJ(I + J)'
--
intersectionP :: (PruferDomain a, Eq a) => Ideal a -> Ideal a -> (Ideal a,[[a]],[[a]])
intersectionP (Id is) (Id js) = case foldr combine ([],[],[]) int of
  ([],_,_)   -> zeroIdealWitnesses is js
  (xs,ys,zs) -> (Id xs,ys,zs)
  where
  -- Compute the inverse of I+J:
  inv = fromId $ invertIdeal (Id is `addId` Id js)

  is' = one : tail is

  -- Compute lengths
  li  = length is'
  lj  = length js

  -- Compute the intersection with witnesses and remove all zeroes and duplicates
  int = nub [ (i <*> j <*> k, addZ m li (j <*> k), addZ n lj (i <*> k))
            | (m,i) <- zip [0..] is'
            , (n,j) <- zip [0..] js
            , k <- inv 
            , i <*> j <*> k /= zero ]
  l   = length int

  addZ n l x = replicate n zero ++ (x:replicate (l-n-1) zero)

  combine (x,y,z) (xs,ys,zs) = (x:xs,y:ys,z:zs)

-- intersectionPD :: (PruferDomain a, Eq a) => Ideal a -> Ideal a -> Ideal a
intersectionPD i@(Id is) j@(Id js) = i `mulId` k
  where
  plm = unMVec $ computePLM_PD (i `addId` j)

  n = length is - 1 
  m = n + length js

  k = Id [ plm !! i !! j | j <- [n+1..m], i <- [0..m]]
--  k = [ "a" ++ show i  ++ show j | j <- [n+1..m], i <- [0..m]]


solvePD :: (PruferDomain a, Eq a) => Vector a -> Matrix a
solvePD x = solveWithIntersection x intersectionP

-- instance (PruferDomain a, Eq a) => Coherent a where
--   solve x = solveWithIntersection x intersectIdeals
