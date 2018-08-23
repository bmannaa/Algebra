module Algebra.Examples.Zn_Examples where

import Data.TypeLevel hiding ((+),(-),(*),mod,Eq,(==))

import Algebra.Zn

-- Some examples:
type Z2 = Zn D2
type Z3 = Zn D3
type Z6 = Zn D6

ex1 = (6 :: Z2) + (3 :: Z2) -- 1 :: Z2
ex2 = (7 :: Z6) + (3 :: Z6) -- 4 :: Z6
-- error: ex3 = (2 :: Z2) + (3 :: Z6)

-- Calculate quotient group Z6/(3)
-- *Zn> quotientGroups (gen (Zn 1 :: Z6)) (gen (Zn 3 :: Z6))
-- [[0,3],[1,4],[2,5]]
