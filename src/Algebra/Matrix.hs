module Algebra.Matrix where

import qualified Data.List as L
import Control.Monad
import Test.QuickCheck

import Algebra.Structures.Rings

-- Row vectors:

data Vector r = Vec [r]
  deriving (Eq)

instance Show r => Show (Vector r) where
  show (Vec vs) = show vs

instance (Eq r, Arbitrary r, Ring r) => Arbitrary (Vector r) where
  arbitrary = do n <- choose (1,10) :: Gen Int
                 liftM Vec $ gen n
    where
    gen 0 = return []
    gen n = do x <- arbitrary
               xs <- gen (n-1)
               if x == zero then return (one:xs) else return (x:xs)

{-
instance Ring r => Ring (Vector r) where
  (Vec xs) <+> (Vec ys) | length xs == length ys = Vec (zipWith (<+>) xs ys)
                        | otherwise = error "Bad dimensions in vector addition"
  (Vec xs) <*> (Vec ys) | length xs == length ys = Vec (zipWith (<*>) xs ys)
                        | otherwise = error "Bad dimensions in vector multiplication"
  -- In order to do these we need to know the length of the vector in advance...
  -- Give me dependent types!
  one  = ?
  zero = ?
-}

unVec :: Vector r -> [r]
unVec (Vec vs) = vs

lengthVec :: Vector r -> Int
lengthVec = length . unVec

-- Matrices:

data Matrix r = M [Vector r]
  deriving (Eq)

instance Show r => Show (Matrix r) where
  show (M xs) = case unlines $ map show xs of
    [] -> "[]"
    xs -> init xs

instance (Eq r, Arbitrary r, Ring r) => Arbitrary (Matrix r) where
  arbitrary = do n <- choose (1,10) :: Gen Int
                 m <- choose (1,10) :: Gen Int
                 xs <- sequence [ liftM Vec (gen n) | _ <- [1..m]]
                 return (M xs)
    where
    gen 0 = return []
    gen n = do x <- arbitrary
               xs <- gen (n-1)
               if x == zero then return (one:xs) else return (x:xs)
               
unM :: Matrix r -> [Vector r]
unM (M xs) = xs

unMVec :: Matrix r -> [[r]]
unMVec = map unVec . unM

vectorToMatrix :: Vector r -> Matrix r
vectorToMatrix = matrix . (:[]) . unVec

matrixToVector :: Matrix r -> Vector r
matrixToVector m | fst (dimension m) == 1 = head (unM m)
                 | otherwise = error "matrixToVector: Bad dimensions"

-- Construct a mxn matrix
matrix :: [[r]] -> Matrix r
matrix xs = 
  let m = fromIntegral $ length xs
      n = fromIntegral $ length (head xs)
  in if length (filter (\x -> fromIntegral (length x) == n) xs) == length xs 
        then M (map Vec xs)
        else error "matrix: Bad dimensions"

dimension :: Matrix r -> (Int, Int)
dimension (M xs) | null xs   = (0,0)
                 | otherwise = (fromIntegral (length xs),fromIntegral (length (unVec (head xs))))

isSquareMatrix :: Matrix r -> Bool
isSquareMatrix (M xs) = all (== length xs) (map lengthVec xs)

-- Transpose a matrix
transpose :: Matrix r -> Matrix r
transpose (M xs) = matrix (L.transpose (map unVec xs))

-- Matrix addition
add :: Ring r => Matrix r -> Matrix r -> Matrix r
add (M xs) (M ys) 
  | dimension (M xs) == dimension (M ys) = 
    matrix (zipWith (zipWith (<+>)) (map unVec xs) (map unVec ys))
  | otherwise = error "Bad dimensions in matrix addition"

-- Matrix multiplication
mul :: Ring r => Matrix r -> Matrix r -> Matrix r
mul (M xs) (M ys) | snd (dimension (M xs)) == fst (dimension (M ys)) = 
                    matrix [ [ foldr1 (<+>) (zipWith (<*>) x y) 
                             | y <- L.transpose (map unVec ys) ]
                           | x <- map unVec xs ]
                  | otherwise = error "Bad dimensions in matrix multiplication"

{-
-- In order to do this the size of the matrix need to be encoded in the type
-- There is also a problem with the fact that it is not possible to add or 
-- multiply matrices with bad dimensions, so the generation of matrices has to be better...
instance Ring r => Ring (Matrix r) where
  (<+>) = add
  (<*>) = mul
  neg (M xs d) = M [ map neg x | x <- xs ] d
  zero  = undefined 
-}

-- Construct a nxn identity matrix 
identity :: IntegralDomain r => Int -> Matrix r
identity n = matrix (xs 0)
  where
  xs x | x == n    = [] 
       | otherwise = (replicate x zero ++ [one] ++ 
                      replicate (n-x-1) zero) : xs (x+1)

propLeftIdentity :: (IntegralDomain r, Eq r) => Matrix r -> Bool
propLeftIdentity a = a == identity n `mul` a
  where n = fst (dimension a)

propRightIdentity :: (IntegralDomain r, Eq r) => Matrix r -> Bool
propRightIdentity a = a == a `mul` identity m
  where m = snd (dimension a)
