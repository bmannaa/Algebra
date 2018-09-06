{-# LANGUAGE EmptyDataDecls #-}
module Algebra.Monomial where

-- | Monomials indexed by their ordering.
data Order ord => Monomial ord = Mon [Integer] deriving Eq

-- | Type class for monomial orderings.
class Order ord where
  comp :: Monomial ord -> Monomial ord -> Ordering

-- | Order implies Ord.
instance Order ord => Ord (Monomial ord) where compare = comp

instance Order ord => Show (Monomial ord) where
  show (Mon []) = []
  show (Mon xs) = concat [ showM x | x <- zip vars xs ]
    where
    vars = ["x","y","z"] ++ [ 'x' : show i | i <- [0..]]
    showM (x,0) = ""
    showM (x,1) = x
    showM (x,n) | n > 0     = x ++ "^" ++ show n
                | otherwise = error "Negative exponent!"

-- | Lexicographical order.
data Lex

instance Order Lex where 
  comp (Mon xs) (Mon ys) = compare xs ys

-- | Graded lexicographical order.
data GrLex

instance Order GrLex where
  comp (Mon xs) (Mon ys) = case compare (sum xs) (sum ys) of
    EQ  -> compare xs ys
    cmp -> cmp
 
-- | Graded reverse lexicographical order.
data GRevLex

instance Order GRevLex where
  comp (Mon xs) (Mon ys) = case compare (sum xs) (sum ys) of
    EQ  -> case signum (last' (filter (/=0) (zipWith' (+) xs (map negate ys)))) of
      -1 -> GT
      0  -> EQ
      1  -> LT
    cmp -> cmp
    where 
    last' xs = if xs == [] then 0 else last xs

-- toLex :: Order ord => Monomial ord -> Monomial Lex
-- toLex = id

-- Test if a monomial divides another monomial.
divides :: Order ord => Monomial ord -> Monomial ord -> Bool
divides (Mon ps) (Mon qs) | length ps > length qs = False
                          | otherwise             = all (>=0) $ zipWith' (-) qs ps

-- Compute the least common multiple of two monomials.
lcmM :: Order ord => Monomial ord -> Monomial ord -> Monomial ord
lcmM (Mon ps) (Mon qs) = Mon (zipWith' max ps qs)

zipWith' :: (a -> a -> a) -> [a] -> [a] -> [a]
zipWith' _ x [] = x
zipWith' _ [] y = y
zipWith' op (x:xs) (y:ys) = (x `op` y) : zipWith' op xs ys
