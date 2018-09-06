{-# LANGUAGE FlexibleInstances, FlexibleContexts, ScopedTypeVariables, OverlappingInstances #-}
module Algebra.MPoly where

import Control.Arrow (second)
import Data.Function (on)
import Data.List (sortBy, permutations, union, transpose, groupBy)
import Data.Map (Map)
import qualified Data.Map as Map
import Test.QuickCheck

import Algebra.Structures.Rings
import Algebra.Structures.Coherent
import Algebra.Structures.StronglyDiscrete
import Algebra.Monomial
import Algebra.Ideals
import Algebra.Q

-- | Multivariate polynomials indexed by the monomial ordering.
--   Constants k are represented as k and an empty monomial list.
data (CommutativeRing r, Order ord) => MPoly r ord = M (Map (Monomial ord) r) 
  deriving (Eq)

-- Convert a list of coefficent and lists of powers to a MPoly.
toMPoly :: (CommutativeRing k, Order ord, Eq k) => [(k,[Integer])] -> MPoly k ord
toMPoly = M .  Map.filter (/=zero) . Map.fromList . map (\(a,b) -> (dropZeros b,a))

-- Convert a monomial to a MPoly.
monToPoly :: (CommutativeRing k, Order ord, Eq k) => Monomial ord -> MPoly k ord
monToPoly (Mon ps) = toMPoly [(one,ps)]

-- Drop all trailing zeroes.
dropZeros :: [Integer] -> Monomial ord
dropZeros = Mon . reverse . dropWhile (==0) . reverse

instance (Show k, CommutativeRing k, Order ord) => Show (MPoly k ord) where
  show (M xs) = tail' 
              $ concatMap (\(Mon xs,n) -> show' (dropZeros xs,n)) 
              $ reverse 
              $ Map.toAscList xs
    where
    show' :: (Monomial ord, k) -> String
    show' (m,x) = case (show x,show m) of
      ("0",_)        -> "+"
      ("1",[])       -> "+1"
      ("-1",[])      -> "-1"
      ("1",m)        -> '+' : m
      ('-':'1':'/':xs,m) -> '-':'1':'/':xs ++ m
      ('-':'1':xs,m) -> '-' : xs ++ m
      ('-':xs,m)     -> '-' : xs ++ m
      (x,m)          -> "+" ++ x ++ m

    tail' []       = "0"
    tail' ('-':xs) = '-':xs
    tail' xs       = tail xs

-- k[x1..xn] is a ring.
instance (CommutativeRing k, Order ord, Eq k) => Ring (MPoly k ord) where
  (M xs) <+> (M ys) = M $ Map.filter (/=zero) $ Map.unionWith (<+>) xs ys
  one               = M (Map.singleton (Mon []) one)
  zero              = M Map.empty
  neg (M xs)        = M $ Map.map neg xs
  (M xs) <*> (M ys) = M $ Map.fromList $ collect $ sortBy (compare `on` fst) 
                        [ (dropZeros (zipWith' (+) n m),x <*> y) 
                        | (Mon n,x) <- Map.toList xs
                        , (Mon m,y) <- Map.toList ys ]
    where
    collect ((a,x):(b,y):xs) | a == b    = collect ((a,x <+> y):xs)
                             | x == zero = collect ((b,y):xs)
                             | otherwise = (a,x) : collect ((b,y):xs)
    collect xs = xs                             

instance (CommutativeRing k, Order ord, Show k, Num k) => Num (MPoly k ord) where
  (+) = (<+>)
  (*) = (<*>)
  (-) = (<->)
  abs = undefined
  signum = undefined
  fromInteger x = toMPoly [(fromInteger x,[])]

-- k[x1..xn] is a commutative ring.
instance (CommutativeRing k, Order ord, Eq k) => CommutativeRing (MPoly k ord) where
  
-- k[x1..xn] is an integral domain.
instance (IntegralDomain k, Order ord, Eq k) => IntegralDomain (MPoly k ord) where

instance Order ord => Arbitrary (MPoly Q ord) where
  arbitrary = do xs <- arbitrary
                 return (toMPoly (map (second (map abs . take 3)) xs))

-- | Leading term.
-- Not really sure why we need forall ord...
lt :: forall ord r. (Order ord, CommutativeRing r, Eq r) => MPoly r ord -> (Monomial ord,r)
lt (M f) | f == Map.empty = (Mon [],zero)
         | otherwise = Map.findMax f 

-- | Leading coefficient.
lc :: (Order ord, Field k, Eq k) => MPoly k ord -> k
lc = snd . lt

-- | Leading monomial.
lm :: (Order ord, CommutativeRing r, Eq r) => MPoly r ord -> Monomial ord
lm = fst . lt

{- 
Division algorithm in k[x1,...,xn]
   
Takes f,f1,...,fs and compute ([a1,...,as],r) s.t:
   
  f = f1a1 + ... + fsas + r

See Cox page 64
-}   
divide :: (Order ord, Field k, Eq k) => MPoly k ord 
                                     -> [MPoly k ord] 
                                     -> ([MPoly k ord], MPoly k ord)
divide f [] = ([],f) -- error "Can't divide with nothing", not sure what to do.
divide f fs = divide' f zero (zip fs (repeat zero)) []
  where
  divide' p r as old 
    | p == zero = (map snd as, r)
    | otherwise = case as of
        []         -> divide' (p <-> lt' p) (r <+> lt' p) (reverse old) []
        ((f,a):as) -> if f == zero
                         then divide' p r as ((f,a):old)
                         else if lm f `divides` lm p
                                 then let ai = a <+> lt p `divLt` lt f
                                          p' = p <-> lt p `divLt` lt f <*> f
                                      in divide' p' r (reverse old ++ (f,ai) : as) []
                                 else divide' p r as ((f,a) : old) 

  lt' = M . uncurry Map.singleton . lt

  divLt (Mon a,b) (Mon c,d) = toMPoly [(b </> d, zipWith' (-) a c)]

-- Specification of the behavior of division in k[x1..xn]
propDivideMPoly :: (Order ord, Field k, Eq k) => MPoly k ord 
                                              -> [MPoly k ord]
                                              -> Bool
propDivideMPoly f fs =  f == sumRing (zipWith (<*>) fs as) <+> r
                     && length fs == length as
  where (as,r) = divide f fs

-- The quotients by division
quotients :: (Order ord, Field k, Eq k) => MPoly k ord -> [MPoly k ord] -> [MPoly k ord]
quotients f = fst . divide f

-- The remainder by division
remainder :: (Order ord, Field k, Eq k) => MPoly k ord -> [MPoly k ord] -> MPoly k ord
remainder f = snd . divide f


-------------------------------------------------------------------------------
-- | Gröbner bases | -- 

-- Compute s-polynomial.
s :: (Field k, Order ord, Eq k) => (MPoly k ord, MPoly k ord) -> MPoly k ord
s (M f,M g) = lcmM (lm (M f)) (lm (M g)) </> lt (M f) <*> M f <-> 
              lcmM (lm (M f)) (lm (M g)) </> lt (M g) <*> M g
  where
  (Mon ps) </> (Mon qs, q) | q == zero = zero
                           | otherwise = toMPoly [(inv q, zipWith' (-) ps qs)]

-- as is not ok!
-- bs is ok!
gbWitness :: (Order ord, Field k, Eq k) 
          => Ideal (MPoly k ord) 
          -> (Ideal (MPoly k ord), [[MPoly k ord]], [[MPoly k ord]])
gbWitness id@(Id xs) = (g,as,bs)
  where
  g@(Id ys) = gb id

  as = [ head [ quotients y x | x <- permutations xs, remainder y x == zero ] | y <- ys ]
  bs = [ quotients x ys | x <- xs ]

-- quickCheckWith stdArgs{ maxDiscard = 10000 } propGbWitnessMPLex 
propGbWitness :: (Field k, Order ord, Eq k) => Ideal (MPoly k ord) -> Bool
propGbWitness id@(Id xs) = 
  let (Id ys, as, bs) = gbWitness id
  in length as == length ys 
     &&
     length bs == length xs
     &&
     and [ y_k == sumRing (zipWith (<*>) a_k xs) && length a_k == length xs
         | (y_k,a_k) <- zip ys as ]
     &&
     and [ x_k == sumRing (zipWith (<*>) b_k ys) && length b_k == length ys
         | (x_k,b_k) <- zip xs bs ]

-- | The Buchberger algorithm for computing Gröbner bases.
gb :: (Order ord, Field k, Eq k) => Ideal (MPoly k ord) -> Ideal (MPoly k ord)
gb (Id []) = Id []
gb (Id fs) = if fs == fs' then reduce (Id fs) else gb (Id fs')
  where
  fs' = fs `union` filter (/=zero) [ remainder (s (f1,f2)) fs | (f1,f2) <- allPairs fs ]
  
  allPairs []     = []
  allPairs (x:xs) = zip (repeat x) xs ++ allPairs xs

-- | Compute reduced Gröbner bases.
-- Cox p89-90
reduce :: (Order ord, Field k, Eq k) => Ideal (MPoly k ord) -> Ideal (MPoly k ord)
reduce (Id fs) = Id $ reduce' [] fs
  where
  reduce' fs' [] = map red fs'
  reduce' fs' (f:fs) | remainder f (fs'++fs) == zero = reduce' fs' fs
                     | otherwise  = reduce' (f:fs') fs
  
  red f | lc f == zero = zero
        | otherwise    = toMPoly [(inv (lc f),[])] <*> f

-- We now get ideal equality k[x1..xn].
instance (Field k, Order ord, Eq k) => Eq (Ideal (MPoly k ord)) where
  x == y = let Id xs = gb x
               Id ys = gb y
           in xs == ys

-- We also get ideal membership.
instance (Field k, Order ord, Eq k) => StronglyDiscrete (MPoly k ord) where
  member f (Id xs) = if r == zero then Just ds else Nothing
    where 
    (Id ys,as,_) = gbWitness (Id xs)
    (cs,r)       = divide f ys
    ds           = [ sumRing (zipWith (<*>) cs a_k) | a_k <- transpose as ]
    

-- Compute the intersection of two ideals using ...
-- If the set of generators is empty then the intersection is the zero ideal.
intersectionMP :: (Field k, Eq k) => Ideal (MPoly k Lex) 
                                  -> Ideal (MPoly k Lex) 
                                  -> (Ideal (MPoly k Lex), [[MPoly k Lex]], [[MPoly k Lex]])
intersectionMP (Id fs) (Id gs) = 
  if zs == [] 
     then zeroIdealWitnesses fs gs
     else ( Id zs 
          , [ fst $ head [ divide z f 
                         | f <- permutations fs
                         , remainder z f == zero ] 
            | z <- zs ]
          , [ fst $ head [ divide z g 
                         | g <- permutations gs
                         , remainder z g == zero ] 
            | z <- zs ]
          )
  where
  t  = toMPoly [(one,[1])]
  zs = [ shiftLeft (M x)
       | M x <- fromId $ gb $ Id $ map ((t <*>) . shiftRight) fs ++ 
                                   map (((one <-> t)<*>) . shiftRight) gs
       , all (==0) (map (\(Mon xs) -> head' xs) (Map.keys x))
       ]

  head' [] = 0
  head' xs = head xs

shiftRight :: (Field k, Order ord) => MPoly k ord -> MPoly k ord
shiftRight (M m) = M (Map.mapKeys (\(Mon xs) -> Mon (0:xs)) m)

shiftLeft :: (Field k, Order ord) => MPoly k ord -> MPoly k ord
shiftLeft (M m) = M (Map.mapKeys (\(Mon xs) -> Mon (tail' xs)) m)
  where
  tail' [] = []
  tail' xs = tail xs

-- Now that it is possible to compute the intersection of two ideals 
-- we now know that k[x1..xn] is coherent.
instance (Field k, Show k, Eq k) => Coherent (MPoly k Lex) where
  solve x = solveWithIntersection x intersectionMP

homogenousDec :: (CommutativeRing r, Order o) => MPoly r o -> [MPoly r o]
homogenousDec (M m) = map (\x -> M $ Map.fromList x) (groupBy f $ sortBy f' l)
               where 
                l = Map.toList m
                f (Mon l1,_) (Mon l2,_) = sum l1 == sum l2
                f' (Mon l1,_) (Mon l2,_) = compare (sum l1) (sum l2)


