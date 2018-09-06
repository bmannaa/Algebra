module Algebra.Test where
import Algebra.Q
import Algebra.Z
factorial n = foldl (*) 1 [1..n]
binom :: Q -> Z -> Q
binom n r = product [i | i<-bnlist n r (toQ 0)] * (1/(toQ $ factorial r))
binrat n = [binom n r | r <- [0..7]] 



bnlist :: Q -> Z -> Q -> [Q]
bnlist n k l | l== kQ = []
             | otherwise = (n - l):bnlist n k (l+1)
          where kQ = toQ k