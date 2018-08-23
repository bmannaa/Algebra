{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}
module Algebra.UPoly where

import Data.List
import Test.QuickCheck
import Control.Monad (liftM)
import Prelude hiding ((^^))
import Algebra.TypeString.Char hiding (Q)
import Algebra.Structures.Rings
import Algebra.Structures.BezoutDomains
import Algebra.Structures.EuclideanDomains
import Algebra.Structures.StronglyDiscrete
import Algebra.Ideals
import Algebra.Q

-- | Polynomials over a commutative ring, indexed by a phantom type x that denote the
-- the name of the variable that the polynomial is of. For example UPoly Q X_
-- is Q[x] and UPoly Q T_ is Q[t] and so on. 
newtype CommutativeRing r => UPoly r x = UP [r]
  deriving (Eq,Ord)

-- | degree the polynomial
deg :: CommutativeRing r => UPoly r x -> Integer
deg (UP xs) | length xs < 2 = 0
            | otherwise = (toInteger $ length xs) - 1

-- Useful shorthand for Q[x].
type Qx = UPoly Q X_

x :: Qx
x = UP [zero,one]

-- Take a list and construct a polynomial by removing all zeroes in the end.
toUPoly :: (CommutativeRing r, Eq r) => [r] -> UPoly r x
toUPoly = UP . reverse . dropWhile (==zero) . reverse

-- | Take an element of the ring and the degree of the desired monomial, for example:
-- monomial 3 7 = 3x^7
monomial :: CommutativeRing r => r -> Integer -> UPoly r x
monomial a i = UP $ replicate (fromInteger i) zero ++ [a]

-- | Compute the leading term of a polynomial.
lt :: CommutativeRing r => UPoly r x -> r
lt (UP []) = zero
lt (UP xs) = last xs

-- | Differentiation for polynomials in k[x].
deriv :: (Num r, CommutativeRing r) => UPoly r x -> UPoly r x
deriv (UP ps) = UP $ zipWith (<*>) (tail ps) (map fromInteger [1..])

-- | Funny integration:
integrate :: (Enum b, Field b, Integral k, Field k, Fractional b) => UPoly k x -> UPoly b x
integrate (UP ps) = UP $ 0.0 : zipWith (/) (map fromIntegral ps) [1..]

instance (CommutativeRing r, Eq r, Show r, Show x) => Show (UPoly r x) where
  show (UP p) = show1 $ toUPoly p
   where
    show1 (UP []) = "0"
    show1 (UP ps) = init $ fixSign $ concat 
                    [ show' (show (undefined :: x)) p n
                    | (p,n) <- zip ps [0..]
                    , p /= zero ]
    
    show' :: (CommutativeRing r, Show r) => String -> r -> Integer -> String
    show' x p 0 = show p ++ "+"
    show' x p 1 = if p == one then x ++ "+" else show p ++ x ++ "+"
    show' x p n = if p == one  
                     then x ++ "^" ++ show n ++ "+" 
                     else show p ++ x ++ "^" ++ show n ++ "+"
    
    fixSign []  = []
    fixSign [x] = [x]
    fixSign ('+':'-':xs) = '-' : fixSign xs
    fixSign (x:xs)       = x : fixSign xs

instance (CommutativeRing r, Eq r, Arbitrary r) => Arbitrary (UPoly r x) where
  arbitrary = liftM (toUPoly . take 5) arbitrary

-- Addition of polynomials.
addUP :: (CommutativeRing r, Eq r) => UPoly r x -> UPoly r x -> UPoly r x
addUP (UP ps) (UP qs) | length ps >= length qs = add' ps qs 
                      | otherwise              = add' qs ps
  where add' a b = toUPoly $ zipWith (<+>) a b ++ drop (length b) a 

-- Multiplication of polynomials.
mulUP :: (CommutativeRing r, Eq r) => UPoly r x -> UPoly r x -> UPoly r x
mulUP (UP ps) (UP qs) = toUPoly $ m ps qs 0
  where
  m ps qs r | r > length ps + length qs - 2 = []
            | otherwise = c r 0 (length ps-1) (length qs-1) : m ps qs (r+1)
  
  c (-1) _ _ _ = zero
  c r k m n | r > m || k > n = c (r-1) (k+1) m n
            | otherwise      = ps !! r <*> qs !! k <+> c (r-1) (k+1) m n

-- | k[x] is the polynomial ring.
instance (CommutativeRing r, Eq r) => Ring (UPoly r x) where
  (<+>)       = addUP
  zero        = UP []
  one         = UP [one]
  neg (UP ps) = UP $ map neg ps
  (<*>)       = mulUP

-- | k[x] is also Num.
instance (Show r, Field r, Num r, Show x) => Num (UPoly r x) where
  (+)    = (<+>)
  (-)    = (<->)
  (*)    = (<*>)
  abs    = fromInteger . d
  signum = undefined -- Is it possible to define this?
  fromInteger x = UP [fromInteger x]

-- | Polynomial rings are commutative.
instance (CommutativeRing r, Eq r) => CommutativeRing (UPoly r x) where

-- | Polynomial rings has a one and are integral domains.
instance (CommutativeRing r, Eq r) => IntegralDomain (UPoly r x) where

-- | Polynomial rings are also Euclidean.
instance (Field k, Eq k) => EuclideanDomain (UPoly k x) where
  d (UP ps)             = fromIntegral (length ps) - 1
  quotientRemainder f g = qr zero f
    where
    -- This is the division algorithm in k[x]. Page 39 in Cox.
      qr q r | d g <= d r = qr (q <+> monomial (lt r </> lt g) (d r - d g))
                               (r <-> monomial (lt r </> lt g) (d r - d g) <*> g)
           | otherwise = (q,r)

{-
    -- This is the division algorithm in k[x]. Page 39 in Cox.
     qr q r | d g <= d r = qr (q <+> monomial (lt r </> lt g) (d r - d g))
                              (r <-> monomial (lt r </> lt g) (d r - d g) <*> g)
            | otherwise = (q,r)
-}
euclid :: (CommutativeRing a, Eq a) => UPoly a x -> UPoly a x -> (UPoly a x, UPoly a x) 
euclid f g | lt g == one = qr zero f
           | otherwise = error "leading coefficient must be a unit"
  where 
   qr q r | deg g <= deg r = qr (q <+> monomial (lt r) (deg r - deg g))
                                (r <-> monomial (lt r) (deg r - deg g) <*> g)
          | otherwise = (q,r)
-- Now that we know that the polynomial ring k[x] is a Bezout domain it is
-- possible to implement membership in an ideal of k[x]. f is a member of the
-- ideal <f1,...,fn> if the rest is zero when dividing f with the principal
-- ideal <h>.
-- instance (Field k, Eq k, Show x) => StronglyDiscrete (UPoly k x) where
--  member p ps = modulo p h == zero 
--    where Id [h] = (\(a,_,_) -> a) $ toPrincipal ps

-- | Square free decomposition of a polynomial 
-- Teo Mora; Solving Polynomial Equations Systems I. pg 69-70
-- Works only for Char 0
--TODO: Add check for char
--square free associate of f
sqfr :: (Num k, Field k) => UPoly k x -> UPoly k x
sqfr f = f `quotient` euclidAlg f f'
            where f' = deriv f

--distinct power factorization aka square free decomposition
sqfrDec :: (Num k, Field k) => UPoly k x -> [UPoly k x]
sqfrDec f = help p q
               where p = euclidAlg f (deriv f)
                     q = f `quotient` p 
                     help p q | d q < 1  = []
                              | otherwise  = t : help (p `quotient` s) s
                              where s = euclidAlg p q
                                    t = q `quotient` s

pgcd :: (Field k, Eq k, Show k) => UPoly k x -> UPoly k x -> (UPoly k x, UPoly k x, UPoly k x, UPoly k x, UPoly k x)
pgcd p q = (r,s,g,p',neg neg_q') 
 where (r,s,g,neg_q',p') = pgcd' p q (one, zero) (zero, one)

-- | the actual computation of the iGCD occurs here except that this one produces
-- (r,s,g,-q',p') such that r p + s q = g, p' g = p, q' g = q
pgcd' :: (Field k, Eq k, Show k) => UPoly k x -> UPoly k x -> (UPoly k x, UPoly k x) 
                                              -> (UPoly k x, UPoly k x) 
                                              -> (UPoly k x, UPoly k x, UPoly k x, UPoly k x, UPoly k x)
pgcd' p q (r,s) (q',p') | q == zero =  (r,s,p,q',p')
                        | p == zero =  (q',p',q,r,s)
                        | deg p < deg q = pgcd' q p (q',p') (r,s)
                        | otherwise = pgcd' (p <-> q2) q (r <-> q2', s <-> p2') (q',p')

                     where t' = UP $ replicate (fromInteger $ deg p - deg q) zero ++ [(inv $ lt q) <*> (lt p)] 
                           (q2,q2',p2') = (t' <*> q, t' <*> q', t' <*> p')
                           
                           
substitute :: (CommutativeRing r) => r -> UPoly r x ->  r
substitute v (UP p)  = foldr (<+>) zero $ zipWith (<*>) p [v^^e | e <-[0..]]


-- | adds a value to the roots of the polynomial
addToRoot :: (CommutativeRing r, Num r) => UPoly r x -> r -> UPoly r x
addToRoot  f@(UP p)  c | deg f == 1 = f
                       | otherwise = foldr (<+>) zero $ zipWith (<*>) (map (\x -> UP [x]) p) (reverse $ lsr n q)
                 where q = UP [neg c,one] 
                       n = deg f
lsr :: (Ring r, Eq r) => Integer -> r -> [r] 
lsr n q | n==0 = [one]
lsr n q | otherwise = (q <*> y) : f
    where f@(y:ys) = lsr (n-1) q

fromUPoly :: (CommutativeRing a) => UPoly a x -> [a]
fromUPoly (UP xs) = xs