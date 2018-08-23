{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}
module Algebra.FormalPowerSeries where

import Test.QuickCheck

import Algebra.Structures.Rings 
import Algebra.Structures.PruferDomains
import Algebra.Q
import Algebra.UPoly
import Data.Stream as St
import Data.List as Lst
import Prelude hiding (map,repeat,zipWith)

--short way to get power series from finite list
ll :: (Ring a) => [a] -> Stream a
ll [] = St.repeat zero
ll (a:as) = a <:> ll as

--power series over a field k
newtype CommutativeRing a => PSeries a x = PS (Stream a) deriving (Ord)

instance (Show a, IntegralDomain a, Eq a, Show y) => Show (PSeries a y) where
  show (PS as) = show (toUPoly $ St.take 20 as :: UPoly a y)

instance (CommutativeRing a, Eq a) => Eq (PSeries a x) where
        PS as == PS bs = (St.take 20 as) == (St.take 20 bs)

--addition and multiplication on streams over commutative ring
(<<+>>) :: (CommutativeRing a) => Stream a -> Stream a -> Stream a
as <<+>> bs = St.zipWith (<+>) as bs

(<<*>>) :: (CommutativeRing a) => Stream a -> Stream a -> Stream a
(Cons a as) <<*>> (Cons b bs) = 
              ll [a <*> b] 
                 <<+>> (zero <:> St.map (a <*>) bs) 
                 <<+>> (zero <:> St.map (<*> b) as) 
                 <<+>> (zero <:> zero <:> as <<*>> bs)

--Power series are Num
instance (Num a, IntegralDomain a, Show a, Show x) => Num (PSeries a x) where
        PS as + PS bs  = PS $ as <<+>> bs
        negate (PS as) = PS $ St.map negate as
        PS as * PS bs  = PS $ as <<*>> bs
        fromInteger 0  = PS $ St.repeat (fromInteger 0)
        fromInteger a  = PS $ (fromInteger a) <:>  (St.repeat $ fromInteger 0)

--substitution --not used
--pseries, almost useless will never terminate
psubst :: (CommutativeRing a) => (PSeries a x) -> a -> a
psubst (PS as) v = ph_subst 0 as v
ph_subst :: (CommutativeRing a) => Integer -> (Stream a) -> a -> a
ph_subst n (Cons b bs) v = ev' n b v <+> ph_subst (n+1) bs v
--polynomial
subst :: (CommutativeRing a) => (UPoly a x) -> a -> a
subst (UP ps) v = foldl (<+>) (zero) $ Lst.map (\(p,c) -> ev' p c v) ([0..] `Lst.zip` ps)
--monomial eval power, coeff, value
ev' :: (CommutativeRing a) => Integer -> a -> a -> a
ev' 0 c v = c
ev' p c v = ev' (p-1) c v <*> v

--The Power series ring 
--Praise them! The Ring-bearers, praise them with great praise! Lord of the Rings
--type Polynomial = UPoly

instance CommutativeRing a => Ring (PSeries a x) where
   PS as <+> PS bs = PS $ as <<+>> bs
   PS as <*> PS bs = PS $ as <<*>> bs
   neg (PS as)     = PS $ St.map neg as
   zero  = PS $ St.repeat zero
   one   = PS $ one <:> St.repeat zero


instance CommutativeRing a => CommutativeRing (PSeries a x) where

instance IntegralDomain a => IntegralDomain (PSeries a x) where



fromPS :: (CommutativeRing a)=> PSeries a x -> Stream  a
fromPS (PS xs) = xs
--fromUPoly :: (CommutativeRing a) => UPoly a x -> [a]
--fromUPoly (UP xs) = xs
toPS :: (CommutativeRing a) => Stream  a -> PSeries  a x
toPS xs = PS $ xs

