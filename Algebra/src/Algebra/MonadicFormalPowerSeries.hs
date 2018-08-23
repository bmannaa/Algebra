{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, UndecidableInstances, TypeSynonymInstances #-}
module Algebra.MonadicFormalPowerSeries where
import Algebra.AlgebraicClosure
import qualified Control.Monad.State.Lazy
import qualified Control.Monad
import Algebra.MPoly
import Algebra.UPoly
import Test.QuickCheck
import Algebra.Structures.Rings
import Algebra.Q
import Algebra.MPoly
import Algebra.TypeString.Char hiding (Q,F,E,R,S)
import qualified Data.List as Lst hiding (take,tail)
import Prelude hiding (map,repeat,zipWith,take,tail,head,map)
import Data.Maybe
import Data.Number.Nat hiding (take,length)

--------type of streams
data (Monad m) => Stream m a = Cons !a !(m (Stream m a))

--head
head :: (Monad m) => Stream m a -> a
head (Cons a _) = a
hd :: (CommutativeRing a, Monad m) => PSeries m a x -> a
hd (PS xs) = head xs
--tail
tail :: (Monad m) => Stream m a -> m (Stream m a)
tail (Cons _ x) = x

tl :: (CommutativeRing a, Monad m) => PSeries m a x -> m (PSeries m a x)
tl (PS xs) = do xs' <- tail xs
                return $ PS xs'
--cons
(<:>) :: Monad m => a -> Stream m a -> Stream m a
a <:> xs = Cons a $ return xs
--monadic map
mapMS :: (Monad m) => (a -> m b) -> Stream m a -> m (Stream m b)
mapMS f g = do y <- f (head g)
               ys <- tail g
               return $ Cons y (mapMS f ys)

--normal map
map :: Monad m => (a -> b) -> Stream m a -> Stream m b
map f (Cons a as) = Cons (f a) z'
                 where z' = do as' <- as
                               return $ map f as'


--zipWith
zipWith :: (Monad m) => (a -> b -> c) -> Stream m a -> Stream m b -> Stream m c
zipWith f (Cons a as) (Cons b bs) = Cons (f a b) z'
                                   where z' = do as' <- as
                                                 bs' <- bs
                                                 return $ zipWith f as' bs'


--addition and multiplication on streams over commutative ring
(<<+>>) :: (CommutativeRing a, Monad m) => Stream m a -> Stream m a -> Stream m a
as <<+>> bs = zipWith (<+>) as bs
{-
(<<*>>) :: (CommutativeRing a, Monad m) => Stream m a -> Stream m a -> Stream m a
(Cons a (as)) <<*>> f@(Cons b bs) = Cons (a <*> b) z'
                           where z' = do bs' <- bs
                                         as' <- as
                                         let d = map (a <*>) bs'
                                         let s = as' <<*>> f
                                         return $ d <<+>> s
-}

(<<*>>) :: (CommutativeRing a, Monad m) => Stream m a -> Stream m a -> Stream m a
as <<*>> bs = mul [] [] as bs
  where
    mul as0 bs0 (Cons a as) (Cons b bs) =
      Cons (sumRing $ Lst.zipWith (<*>) (a : as0) (reverse $ b : bs0)) $ do
        as' <- as
        bs' <- bs
        return $ mul (a:as0) (b:bs0) as' bs'
--stupid, just to make the instance num work
instance (Show a) => Show (PSeries m a x) where
        show x = ""
instance (Num a, IntegralDomain a, Show a, Show x, Monad m) => Num (PSeries m a x) where
        PS as + PS bs  = PS $ as <<+>> bs
        negate (PS as) = PS $ map negate as
        PS as * PS bs  = PS $ as <<*>> bs
        fromInteger 0  = zero 
        fromInteger a  = PS $ ll [fromInteger a] 

--repeats the monadic function 
rep :: (Monad m) => Int -> (a -> m a) -> a -> m [a]
rep 0 _ _ = return []
rep n f a = do a' <- f a
               xs <- rep (n-1) f a'
               return (a':xs)


--Praise them! The Ring-bearers, praise them with great praise! Lord of the Rings
--type Polynomial = UPoly

strZero :: (Ring a, Monad m) => Stream m a
strZero = Cons zero (return $ strZero)
strOne :: (Ring a, Monad m) => Stream m a
strOne = Cons one (return $ strZero)

instance (CommutativeRing a, Monad m) => Ring (PSeries m a x) where
   PS as <+> PS bs = PS $ as <<+>> bs
   PS as <*> PS bs = PS $ as <<*>> bs
   neg (PS as)     = PS $ map (neg) as
   zero  = PS $ strZero
   one   = PS $ strOne

instance (CommutativeRing a, Eq a, Monad m) => Eq (PSeries m a x) where
  PS (Cons a as) == PS (Cons b bs) = False
instance (CommutativeRing a, Monad m) => CommutativeRing (PSeries m a x) where

instance (IntegralDomain a, Monad m) => IntegralDomain (PSeries m a x) where

newtype (CommutativeRing a, Monad m) => PSeries m a x = PS (Stream m a)

fromPS :: (CommutativeRing a, Monad m) => PSeries m a x -> Stream m a
fromPS (PS xs) = xs
fromUPoly :: (CommutativeRing a) => UPoly a x -> [a]
fromUPoly (UP xs) = xs
toPS :: (CommutativeRing a, Monad m) => Stream m a -> PSeries m a x
toPS xs = PS $ xs

--short way to get power series from finite list
ll :: (Ring a, Monad m) => [a] -> Stream m a
ll [] = strZero
ll (a : as) = a <:> ll as


fstM :: (Monad m) => m (a,b) -> m a
fstM = Control.Monad.liftM fst
sndM :: (Monad m) => m (a,b) -> m b
sndM = Control.Monad.liftM snd
{-
--test termination mapMS and map
-- mapMS  (head . snd . Lst.head) (apply (mapMS tt1 tt2) ())
-- map  head (map ttx tt2)
--zipWith ((head . snd . Lst.head))(apply (tail (zipWith (+) tt3 tt3)) ())
-- !!!  apply (tt3 !!! 2) ()
-- <<+>> head (tq2 <<+>> tq3)
-- <<*>> head (tq2 <<*>> tq3)
ttx :: Int -> Int

ttx = \n -> n+1
tt1 :: Int -> ST s Int
tt1 n = return $ n

tt2 :: Stream (ST s) Int
tt2 = Cons (0, ST $ \ s -> [(s,tt3)])

tt3 :: Stream (ST s) Int
tt3 = Cons (2, ST $ \ s -> [(s,tt2)])

ttq1 :: (Field k, Eq k, Show k) => UPoly (R k) x -> ST (S k) (UPoly (R k) x)
ttq1 n = putDBoth [] [one] n (n <+> one) --return $ n


ttq6 :: (Field k, Eq k, Show k) => (R k) -> ST (S k) (R k)
ttq6 n = putDBoth [] [one] n (n <+> one) --return $ n

ttq2 :: Stream (ST (S Q)) (R Q)
ttq2 = Cons (toMPoly [(2,[]),(1,[0,1])] :: (R Q) , ST $ \ s -> [(s,ttq3)]) 

ttq3 :: Stream (ST (S Q)) (R Q)
ttq3 = Cons (toMPoly [(1,[]),(2,[0,1])] :: (R Q) , ST $ \ s -> [(s,ttq2)]) 

tq2 :: Stream (ST s) (R Q)
tq2 = Cons (toMPoly [(1,[])] :: R Q, ST $ \ s -> [(s,tq3)])

tq3 :: Stream (ST s) (R Q)
tq3 = Cons (toMPoly [(2,[])] :: R Q, ST $ \ s -> [(s,tq2)])

tx :: Int -> Int
tx = \n -> n+1

t1 :: Int -> Duhl Int
t1 n = return $ n+1

t2 :: Stream Duhl Int
t2 = Cons (0, Duhl t2)

t3 :: Stream Duhl Int
t3 = Cons (2, Duhl t2)

ttq2' :: Stream Duhl Q
ttq2' = Cons (0 :: Q, Duhl ttq2')

ttq3' :: Stream Duhl Q
ttq3' = Cons (2 :: Q, Duhl ttq2')

newtype Duhl a = Duhl a
unDuhl (Duhl a) = a
instance Monad Duhl where
  (Duhl f) >>= k = k f
  return a = Duhl a

instance (Monad m, Show a) => Show (Stream m a) where
  show (Cons (a, as)) = show a
-}