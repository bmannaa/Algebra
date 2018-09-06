{-# LANGUAGE ScopedTypeVariables, FlexibleContexts #-}

module Tools.NewtonMain where
import Algebra.UPoly
import Algebra.MPoly
import Algebra.Structures.FieldOfFractions hiding (inverse)
import Algebra.FieldOfRationalFunctions
import Algebra.Structures.Rings
import Algebra.Q
import qualified Data.Map
import qualified Algebra.Z
import Data.List
import Algebra.TypeString.Char hiding (Q, R, S, F, E)
import Algebra.NewtonTheorem
import Algebra.AlgebraicClosure
import Algebra.FormalPowerSeries
import Data.Maybe
import IO ( stdin, hGetContents )
import System ( getArgs, getProgName )


import Tools.LexNewtonGrammar
import Tools.ParNewtonGrammar
import Tools.SkelNewtonGrammar
import Tools.PrintNewtonGrammar
import Tools.AbsNewtonGrammar
import Tools.Prep
import Tools.ErrM

type ParseFun a = [Token] -> Err a

myLLexer = myLexer

type Verbosity = Int


parse :: (Print a, Show a) => ParseFun a -> String -> IO a
parse p s = let ts = myLLexer s' in case p ts of
              Bad s    -> error ("parse error"++ s') 
              Ok  tree -> return $ tree 
                            
        where s' = prep s


showTree :: (Show a, Print a) => a -> IO ()
showTree tree
 = do
      putStrLn $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrLn $ "\n[Linearized tree]\n\n" ++ printTree tree

main :: IO ()
main = do --putStrLn "enter a monic polynomial in X Y (i.e.1 + X Y + 2 X^2 Y - 3 X Y^2 + Y^3)"
          polyStr <- getLine 
          --let polyStr = "1 + X Y + 2 X^2 Y - 3 X Y^2 + Y^3"
          --let polyStr1 = prep polyStr
          parsedPoly <- parse pYP polyStr
          let p = absToPoly parsedPoly
          let result = apply (run $ newton p) []
          putStrLn $ unlines $ pretPrin result
          --main

pretPrin :: [(S Q, (Q, [UPoly (UPoly (R Q) V_) W_]))] -> [String]
pretPrin = map pp1

pp1 :: (S Q, (Q, [UPoly (UPoly (R Q) V_) W_])) -> String
pp1 (state, res) = "State: " ++ pp2 state ++ "\n" ++ "Result: " ++ pp3 res ++ "\n"


pp2 :: S Q -> String
pp2 st = concat $ intersperse "," $ map ((++"=0"). varsToRoots . show) st

pp3 :: (Q, [UPoly (UPoly (R Q) V_) W_]) -> String
pp3 (e, xs) = concat $ intersperse " " $ map (pp4 e) xs

pp4 :: Q -> UPoly (UPoly (R Q) V_) W_ -> String
pp4 n (UP [r,y]) = "(Y" ++ (if (head root) == '-' then root else ('+':root)) ++ ")"
         where root = (varsToRoots . (replace 'v' 'X') . customShow n) r ++ "+ ..."
pp4 _  _         = error "NewtonMain.pp4: polynomial is not linear"

powers :: Q -> [Q]
powers n = map ((n <*>) . toQ ) [0..]

powz :: [Algebra.Z.Z]
powz = [0..]

customShow :: (Field k, Show k, Eq k) => Q -> UPoly (R k) V_ -> String 
customShow u (UP ps) | null ls = "0"
--customShow u (UP []) = "0"
                     | u==one  = init $ fixSign' $ concat
                                    [ show' (show (undefined :: V_)) p n 
                                    | (p,n) <- zip ps [0..]
                                    , p /= zero ]
                     | otherwise = init $ fixSign' $ concat
                                    [ show'' (show (undefined :: V_)) p n 
                                    | (p,n) <- zip ps (powers u)
                                    , p /= zero ]
    where
    ls = dropWhile (==zero) ps 
    show'' :: (Field k, Show k, Eq k) => String -> (R k) -> Q -> String
    show'' x p n | n==zero = show p ++ "+"
                 | n==one  = if p==one then x ++ "+" 
                               else (if p==(neg one) then "-" ++ x ++ "+" else showc p ++ x ++ "+")
                 | otherwise = if p == one
                                 then x ++ "^" ++ show n ++ "+"
                                 else if p==(neg one) 
                                         then "-" ++ x ++ "^" ++ show n ++ "+" 
                                         else showc p ++ x ++ "^" ++ show n ++ "+"

    show' :: (Field k, Show k, Eq k) => String -> (R k) -> Integer -> String
    show' x p n | n==zero = show p ++ "+"
                | n==one  = if p==one then x ++ "+" 
                               else (if p==(neg one) then "-" ++ x ++ "+" else showc p ++ x ++ "+")
                | otherwise = if p == one
                                 then x ++ "^" ++ show n ++ "+"
                                 else if p==(neg one) 
                                         then "-" ++ x ++ "^" ++ show n ++ "+" 
                                         else showc p ++ x ++ "^" ++ show n ++ "+"
                       
    fixSign' []  = []
    fixSign' [x] = [x]
    fixSign' ('+':'-':xs) = '-' : fixSign' xs
    fixSign' (x:xs)       = x : fixSign' xs


showc :: (Field k, Show k, Eq k) => R k -> String
showc f@(M x) | Data.Map.size x < 2 = show f
              | otherwise  = "(" ++ show f ++ ")" 

replace :: Eq a => a -> a -> [a] -> [a]
replace x y = map (\z -> if z == x then y else z)

varsToRoots :: String -> String
varsToRoots [] = []
varsToRoots [x] | lu x == Nothing = [x]
                | otherwise       = fromJust $ lu x

varsToRoots (x:y:xs) | lu x == Nothing      = x : varsToRoots (y:xs)
                     | x /= 'x'             = (fromJust $ lu x) ++ varsToRoots (y:xs)
                     | lu' [x,y] == Nothing = (fromJust $ lu x) ++ varsToRoots (y:xs)
                     | otherwise            = (fromJust $ lu' [x,y]) ++ varsToRoots xs
lu :: Char -> Maybe String
lu a = lookup [a] tVarRoot           
lu' :: String -> Maybe String
lu' a = lookup a tVarRoot

origVars = ["x","y","z"] ++ [ 'x' : show i | i <- [0..10]]
rootVars = ["a","b","c","d"] ++ [ "a_" ++ show i | i <- [0..9]]
tVarRoot = zip origVars rootVars

absToPoly :: YP -> UPoly (UPoly Q V_) W_
absToPoly = (foldl1 (<+>)) . (map yPoly) . (map (foldl1 sumXPoly)) . (groupBy crit) . xPoly . absToList

yPoly :: (UPoly Q x, Integer) -> UPoly (UPoly Q x) y
yPoly (c, yDeg) = monom 
      where monom = UP $ replicate (fromInteger yDeg) zero ++ [c]

sumXPoly :: (UPoly Q x, Integer) -> (UPoly Q x, Integer) -> (UPoly Q x, Integer)
sumXPoly (p1,i) (p2,j) | i /= j = error "something wrong"
                       | otherwise = (p1 <+> p2, i)
 
crit :: (a,Integer) -> (a,Integer) -> Bool
crit (_,i) (_,j) = i==j

xPoly :: [(Q,Integer,Integer)] -> [(UPoly Q x,Integer)]
xPoly [] = []
xPoly ((c, xDeg, yDeg):xs) = (monom, yDeg): xPoly xs
      where monom = UP $ replicate (fromInteger xDeg) 0 ++ [c]

absToList :: YP -> [(Q,Integer,Integer)]
absToList (YPMulti y1 y2) = absToList y1 ++ absToList y2
absToList (YPSing y)      = [termToTriple y]

termToTriple :: Term -> (Q, Integer, Integer)
termToTriple (TermConst c) = (sCoeffToQ c, 0, 0)
termToTriple (TermNonConst c m) = (sCoeffToQ c, fst $ mt, snd $ mt) 
                 where mt = monomToDegs m

monomToDegs :: Mon -> (Integer, Integer)
monomToDegs (MonomX (XMonom i)) = (i,0)
monomToDegs (MonomY (YMonom i)) = (0,i)
monomToDegs (MonomXY (XMonom i) (YMonom j)) = (i,j) 

sCoeffToQ :: SCoeff -> Q
sCoeffToQ (SCoeffP x) = coeffToQ x
sCoeffToQ (SCoeffM x) = neg $ coeffToQ x

coeffToQ :: Coeff -> Q
coeffToQ (CoeffR i j) = coeffToQ i <*> (inv $ coeffToQ j)
coeffToQ (CoeffI i)   = toQ i
