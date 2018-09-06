{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}

module Algebra.TwoVariatePoly where
import Data.List (sortBy, permutations, union, transpose, groupBy)
import qualified Data.Map as Mp
import Algebra.TypeString.Char hiding (Q, R, S)
import Algebra.Structures.Rings
import Algebra.Structures.Coherent
import Algebra.Structures.StronglyDiscrete
import Algebra.Monomial
import Algebra.Ideals
import Algebra.Q
import Algebra.MPoly
import Algebra.UPoly
import Algebra.Structures.FieldOfFractions
import Prelude hiding ((^^))

data (CommutativeRing r) =>  TwoVarPoly r x y= TVP [((Int,Int),r)]

instance (CommutativeRing r, Eq r) => Ring (TwoVarPoly r x y) where
  (TVP xs) <+> (TVP ys) = TVP $ Mp.toList $ Mp.filter (/=zero) $ Mp.unionWith (<+>) (Mp.fromList xs) (Mp.fromList ys)
  one                   = TVP [((0,0),one)]
  zero                  = TVP []
  neg (TVP xs)          = TVP $ map (\(c,a) -> (c, neg a)) xs
  (TVP xs) <*> (TVP []) = zero
  (TVP []) <*> (TVP xs) = zero
  (TVP xs) <*> (TVP ys) = TVP $ collect  
                        [ ((fst n + fst m, snd n + snd m),x <*> y) 
                        | (n,x) <- xs
                        , (m,y) <- ys ]

instance (CommutativeRing a, Eq a) => CommutativeRing (TwoVarPoly a x y) where
{-
    where
    collect ((a,x):(b,y):xs) | a == b    = collect ((a,x <+> y):xs)
                             | x == zero = collect ((b,y):xs)
                             | otherwise = (a,x) : collect ((b,y):xs)
    collect xs = xs                             
-}

fs' ([a,b],_) ([c,d],_) = compare (a+b) (c+d)
fr ((a,b),_) ((c,d),_) = a+b == c+d

dropZeros ::(Ring r, Eq r) => [((a,b),r)] -> [((a,b),r)]
dropZeros x = filter (\((_,_),c) -> c /=zero) x

tvpHomogenousDec :: (CommutativeRing r) => TwoVarPoly r x y-> [TwoVarPoly r x y]
tvpHomogenousDec (TVP m) =  map (\x -> TVP x) (groupBy fr $ sortBy fs m)

tvpToUP :: (CommutativeRing r, Eq r) => TwoVarPoly r x y-> UPoly (UPoly r x) y
tvpToUP (TVP as) = as5
   where
     as1 = groupBy fg' $ sortBy fs' as
     as2 = map (sortBy fn') as1
     as3 = map (\x -> (tn x, map tz x)) as2
     as4 = map (\(a,x) -> (a,UP x)) $ map (\(a,b)-> (a,lk b))  $ map (\(a,b) -> (a, le b)) as3
     as5 = UP $ lk $ le as4
     fs' ((_,b),_) ((_,d),_) = compare b d
     fg' ((_,b),_)((_,d),_)  = b == d 
     fn' ((a,_),_) ((c,_),_) = compare c c
     tn = snd . fst . head
     tz ((a,b),c) = (a,c)
     lk :: CommutativeRing a => [(Int, a)] -> [a]
     lk [] = []
     lk ((a,b):[]) = b:[]
     lk ((a,b):(c,d):xs) | c /= a+1 = b:lk ((a+1,zero):(c,d):xs)
                         |otherwise = b:lk ((c,d):xs)
     le :: CommutativeRing a => [(Int, a)] -> [(Int, a)]
     le xs | (fst $ head xs) /= 0 = (0,zero):xs
           | otherwise = xs

upToTVP :: (CommutativeRing r, Eq r) => UPoly (UPoly r x) y -> TwoVarPoly r x y 
upToTVP (UP as) = TVP as3
   where
    as0 = map (\(UP x) -> x) as
    as1 = map (zip [0..]) as0
    as2 = zip [0..] as1
    as3 = concatMap (\(n, ls) -> map (\(m,a) -> ((m,n),a)) ls) as2

polyF :: UPoly (UPoly Q X_) Y_
polyF=UP [UP [0,1,2,3],UP [1,2,3,4], UP [2,3,4,5],UP [3,4,5,6],UP [4,5,6,7],UP [5,6,7,8]]


instance (CommutativeRing r, Eq r, Show r, Show x, Show y) => Show (TwoVarPoly r x y) where
  show (TVP p) = show1 $ TVP $ sortBy fs $ dropWhile (\((_,_),a) -> a == zero) p
   where
    show1 (TVP []) = "0"
    show1 (TVP ps) = init $ fixSign $ concat 
                    [ show' "X" "Y" p m n
                    | ((m,n),p) <- ps, p /= zero ]
    
    show' :: (CommutativeRing r, Show r, Eq r) => String -> String -> r -> Int -> Int-> String
    show' x y p 0 0 = show p ++ "+"
    show' x y p m n = if p == one then 
                         br x m ++ br y n  ++ "+" 
                         else if p == (neg one) then 
                                 "-" ++  br x m ++ br y n  ++ "+" 
                              else show p ++ br x m ++ br y n  ++ "+"
    
    br :: String -> Int -> String
    br x 0 = ""
    br x 1 = x
    br x n = x ++ "^" ++ show n

    fixSign []  = []
    fixSign [x] = [x]
    fixSign ('+':'-':xs) = '-' : fixSign xs
    fixSign (x:xs)       = x : fixSign xs


substitute :: (CommutativeRing r) => r -> r -> TwoVarPoly r x y -> r
substitute a b f = advSubstitute id a b f
--substitute a b (TVP p) = foldr (<+>) zero $ map (\((x,y),c) -> a^^x <*> b^^y <*> c) p


changeVar :: (CommutativeRing r, Eq r) => FieldOfFractions (TwoVarPoly r x y)  -> FieldOfFractions (TwoVarPoly r w z) 
                                     -> FieldOfFractions (TwoVarPoly r w z) -> FieldOfFractions (TwoVarPoly r w z)

changeVar (F(no,deno)) f1 f2 = (qq no) <*> inv (qq deno)
       where qq = advSubstitute (\r -> toFieldOfFractions (TVP [((0,0),r)])) f1 f2 



advSubstitute :: (CommutativeRing r, CommutativeRing s) => (r->s) -> s -> s -> TwoVarPoly r x y -> s
advSubstitute f a b (TVP p) = foldr (<+>) zero $ map (\((x,y),c) -> a^^x <*> b^^y <*> (f c)) p

xly :: (Eq c) => ((c,c),a) -> ((c,c),b) -> Bool
xly (a,_) (b,_) = (a==b)

fs ((a,b),_) ((c,d),_) = compare (a+b) (c+d)

xty :: (Eq a, Ord a) => ((a,a), b) -> ((a,a),c) -> Ordering
xty ((a,b),_) ((c,d),_) | a == c = compare b d
                        | otherwise = compare a c


ylk :: CommutativeRing a => [(Int, a)] -> [a]
ylk [] = []
ylk ((a,b):[]) = b:[]
ylk ((a,b):(c,d):xs) | c /= a+1 = b:ylk ((a+1,zero):(c,d):xs)
                     | otherwise = b:ylk ((c,d):xs)


yle :: CommutativeRing a => [(Int, a)] -> [(Int, a)]
yle xs | (fst $ head xs) /= 0 = (0,zero):xs
       | otherwise = xs

collect :: (Ring r, Eq a, Ord a) => [((a,a),r)] -> [((a,a),r)]
collect = map (\xs -> (fst $ head xs, foldr (\x y -> snd x <+> y) zero xs)) . groupBy xly . sortBy xty

tvpToLst y = (\(TVP x) -> x)y


instance (CommutativeRing r, Eq r) => Eq (TwoVarPoly r x y) where
 (TVP p1) == (TVP p2) = p1==p2