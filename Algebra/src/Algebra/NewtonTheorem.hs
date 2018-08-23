module Algebra.NewtonTheorem where
import Algebra.Structures.FieldOfFractions hiding (inverse)
import Algebra.FieldOfRationalFunctions
import Algebra.AlgebraicClosure hiding (qr)
import Algebra.Structures.EuclideanDomains hiding (modulo,  quotient)
import Algebra.FormalPowerSeries
import Data.Stream 
import Algebra.UPoly
import Algebra.Structures.Rings
import Algebra.NonMonadicHenselLemma
import Algebra.MPoly
import Control.Monad
import qualified Data.Map as Mp
import Algebra.Q
import Prelude hiding (head,tail,map,take)
import qualified Data.List as Lst
import Algebra.TypeString.Char hiding (Q, R, S, F, E)
import Debug.Trace

tracer a b | trace ("tracer: " ++ show a ++ " " ++ show b) False = undefined
tracer a b = trace ("tracer " ++ show a ++ " " ++ show b)
-- | given a polynomial returns two coprime (not necessarily irreducible) factors of this polynomial -if any exist-
twoCopDec :: (Field k, Eq k, Show k, Num k, Show y) => UPoly (R k) y -> ST (S k) (UPoly (R k) y, UPoly (R k) y)
twoCopDec  f@(UP p) = do (fy, fy_deg) <- iDeg f
                         case (fy_deg < 2) of
                          True  -> error "polynomial must be nonlinear"
                          False -> do r <- root f --f should be monic --check!!
                                      let fac = UP [neg r, one]
                                      (d,e) <- multiplicity fac f
                                      (d2, d2_deg) <- iDeg e
                                      case (d2_deg == 0 || d2_deg == fy_deg) of
                                       True -> error "no coprime factors"
                                       False -> return (d,d2)
                                             
-- | given a polynomial f and a factor p of this polynomial 
-- returns the p^n f/p^n for some n such that p^n f/p^n are coprime
multiplicity :: (Field k, Eq k, Show k, Num k, Show y) => UPoly (R k) y -> UPoly (R k) y -> ST (S k) (UPoly (R k) y, UPoly (R k) y)
multiplicity  fac  f = do 
                          let (qt, rm) = f `euclid` fac
                          sta <- get
                          --if True then error ("state:" ++ show sta ++ ", fac: " ++ show fac ++ ", f:" ++ show f ++ ", qt:" ++ show qt ++ ", rm:" ++ show rm) else error ""
                          rmZero   <-  iszerop rm
                          case (rmZero) of
                           False -> return (one, f)
                           True  -> do (fac2, rest) <- multiplicity fac qt
                                       return (fac <*> fac2, rest)


-- | the main function given a polynomial in y with polynomial coeff in X returns 
-- a tuple, the second of the tuple is alist of linear factors of the given polynomial, these are polynomials
-- with power series coefficients. The first of the tuple is a rational number t such that the input indeterminate X^t is
-- equal to the new indeterminat X in the factors
newton :: (Num k, Field k, Eq k, Show k, Show x, Show y) => UPoly (UPoly k x) y -> ST (S k) (Q, [F (R k) x y])
newton  f@(UP p) = do let f1   = UP $ Lst.map toFieldOfFractions p
                      let tst  = euclidAlg f1 (deriv f1)
                      case (deg tst > 0 || tst== zero) of
                       True  -> error "Newton: gcd f f' must be 1"
                       False -> do let f2 = embed f
                                   (i, facs) <- newton1 f2
                                   return (inv $ toQ i, facs)

embed :: (CommutativeRing r, Eq r) => UPoly (UPoly r x) y -> UPoly (PSeries (R r) x) y
embed (UP p) = UP $ Lst.map (\(UP x) -> PS $ ll $ Lst.map (\y -> toMPoly [(y,[])]) x) p 

--logI :: String -> String -> ()
--logI x y = unsafePerformIO $ putStrLn (x++":"++y)
-- | actual factorization occurs here, same description as newton function, except that the first of the tuple is
-- the inverse of the value in function newton
newton1 :: (Num k, Field k, Eq k, Show k, Show x, Show y) => F (R k) x y -> ST (S k) (Integer, [F (R k) x y])
newton1  f@(UP p)    | deg f < 2 = return (1, [f])
                     | otherwise = do
                                      let f1 = addToRoot f c --killing the n-1^th coeff
                                      (ordOfMin, indOfMin, f2) <- mulDownRoot f1 --multiplying root F(0,0) /= 0 
                                      let f2y = proj_y f2 --the y projection f2(0,Y)
                                      --tracer "y-projection" $ show f2y
                                      (f2y1, f2y2) <- twoCopDec f2y --two coprime factors of f2(0,Y)
                                      (r,s,g,_,_)  <- sGCD f2y1 f2y2
                                      sta <- get
                                      let (f21, f22) = lemma f2 f2y1 f2y2 r s --Hensel's lemma
                                      (i,  f21factors) <- newton1 f21 --factorizing the decomposition
                                      (j,  f22factors) <- newton1 f22
                                      let k = lcm i j                 -- Coeff of f21fac in x', x'^m = x
                                      let ki = k `div` i              -- Coeff of f22fac in x'', x''^n = x
                                      let kj = k `div` j              -- we turn both into coeff in x1, x1^{lcm m n} = x
                                      let f21Facs = adjustFacsCoeff ki f21factors -- new factors in X'^k = X
                                      let f22Facs = adjustFacsCoeff kj f22factors
                                      let factors1 = f21Facs ++  f22Facs
                                      let d = ordOfMin * k
                                      let factors2 = shiftUpFacs d factors1  --reversing the X^-di multiplication
                                      let c1 = raiseIndExponent (k * indOfMin) c --the added to the right indet
                                      let factors3 = subtractRoot (UP [c1]) factors2
                                      return (indOfMin * k, factors3)
                  where adjustFacsCoeff i fs =  Lst.map (UP . (Lst.map $ raiseIndExponent i) . fromUPoly) fs
                        subtractRoot r fs = Lst.map (<+> r) fs
                        nMin1Coeff = last (init p)
                        c = PS $ map (`divByBase` fromInteger (deg f)) (fromPS nMin1Coeff)
                       

shiftUpFacs :: (CommutativeRing r) => Integer -> [F r x y] -> [F r x y]
shiftUpFacs d  xs | d==0 = xs
                  | otherwise = Lst.map (shiftUpFac d) xs
       where shiftUpFac d (UP p) = UP $ (PS $ Cons zero (shift (d-1) t)) : Lst.tail p
                                     where (PS t) = Lst.head p
  



-- TODO : Description -quite complicated-
--This is not general multiplication
--general multiplication requires use of field of fractions of powerseries!!
mulDownRoot :: (Field k, Show k, Num k) => F (R k) x y-> ST (S k) (Integer, Integer, (F (R k) x y))
mulDownRoot  f@(UP p) | deg f < 2 = error "mulDownRoot: constant or linear polynomial"
                      | otherwise = do let p1 = init p
                                       (ordOfMin, indOfMin) <- od 0 (reverse p1)
                                       let ps = Lst.map (raiseIndExponent indOfMin) p
                                       let newf = reducePower ordOfMin (UP ps)
                                       return (ordOfMin, indOfMin, newf)

                 where od i q = do let h = Lst.map hd q
                                   --us <- findIndicesM isUnit h
                                   st <- get
                                   let us = Lst.map (modState st) h
                                   let us' = Lst.map (toInteger) $ Lst.findIndices (/= zero) us
                                   case us' of
                                    [] -> do let q1 = Lst.map tl q 
                                             od (i+1) q1 
                                    ind -> do let o = i
                                              let j = last ind + 1 
                                              let g = gcd o j
                                              return ((o `div` g) , (j `div` g))
                                             

-- | reduces the powers of the power series coeffs by decreasing 
-- Y^n + a1(X) Y^n-1 + .. + an(X) -> Y^n + a1(X) X^-d Y^n-1 + .. + an(X) X^-dn 
reducePower :: (Field k, Show k, Eq k) => Integer -> F (R k) x y -> (F (R k) x y)
reducePower  j  f@(UP p) = UP $ Lst.map (\(p,i) -> rdpow (j*i) p) $ Lst.zip p (reverse [0..(toInteger $ length p)-1])

-- | removes the first n elements of a power series, if those elements are zero this is equivalent to multiplying by X^-n
rdpow :: (CommutativeRing a) => Integer -> PSeries a x -> (PSeries a x)
rdpow 0  f = f
rdpow 1  f = tl f
rdpow i  f = rdpow (i-1) $ tl f 

-- | raises the exponents of the indeterminate of a power series by a given value for example X -> X^4
raiseIndExponent :: (CommutativeRing a) => Integer -> PSeries a x -> PSeries a x
raiseIndExponent i (PS (Cons a as))   | i <= 0 = error "raiseIndExponent: power should be > 0"
                                      | i == 1 = PS (Cons a as)
                                      | otherwise = PS $ Cons a  (intersperse as i)
                           where intersperse (Cons b bs) i = shift (i-1) $ Cons b (intersperse bs i)
-- | shifts the exponent of the indeterminant by the given value (must be positive)
shift :: (CommutativeRing a) => Integer -> Stream a -> Stream a
shift  j  as | j == 0 = as
             | otherwise = shift (j-1) $ Cons zero (as)

-- | similar to Data.List.indices but with a monadic function as an argument
findIndicesM :: (Monad m) => (a -> m Bool) -> [a] -> m [Integer]
findIndicesM  f  xs = fi f xs 0
        where fi f [] n     = return []
              fi f (x:xs) n = do b <- f x 
                                 case b of
                                  False -> fi f xs (n+1)
                                  True  -> do ns <- fi f xs (n+1)
                                              return (n:ns)
-- | test if an element is a unit
{-

-- | Given the result of Newton theorem it returns a diplayable result, taking only few elements of each power series coeff
run  :: (Field k, Eq k, Show k) => ST (S k) (Q, [F (R k) z y])
                                      -> ST (S k) (Q, [UPoly (UPoly (R k) z) y])
run  factors = do (i,xs) <- factors
                  ps <- mapM (\(UP p) -> liftM UP $ mapM forshow p) xs
                  return (i, ps)

forshow :: (Field k, Eq k, Show k) => (PSeries (R k) x) -> ST (S k) (UPoly (R k) x)
forshow (PS xs) = liftM (toUPoly) $ mapM modState (take 1 xs)
-}

-- | Given the result of Newton theorem it returns a diplayable result, taking only few elements of each power series coeff
run  :: (Field k, Eq k, Show k) => ST (S k) (Q, [F (R k) z y])
                                      -> ST (S k) (Q, [UPoly (UPoly (R k) z) y])
run  factors = do (i,xs) <- factors
                  ps <- mapM (\(UP p) -> liftM UP $ mapM forshow p) xs
                  return (i, ps)

forshow :: (Field k, Eq k, Show k) => (PSeries (R k) x) -> ST (S k) (UPoly (R k) x)
forshow (PS xs) = do st<- get
                     let t = Lst.map (modState st) (take 5 xs)
                     return (UP t)

