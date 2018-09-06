{-# LANGUAGE ScopedTypeVariables, FlexibleContexts, FlexibleInstances #-}
module Algebra.HenselLemma where
import Algebra.MPoly
import Algebra.MonadicFormalPowerSeries
import Algebra.AlgebraicClosure
import Algebra.UPoly
import Test.QuickCheck
import Algebra.Structures.Rings
import Algebra.Q
import Algebra.TypeString.Char hiding (Q,F,E,R,S)
import qualified Data.List as Lst
import Prelude hiding (map,repeat,zipWith,head,tail)
import Control.Monad

-- | the type of polynomials with power series coeff
type F m a x y = UPoly (PSeries m a x) y 
-- | the type of power series with polynomial coeff
type E m a y x = PSeries m (UPoly a y) x

--test case
a_2X :: PSeries (ST s) (R Q) X_
a_2X = one
a_1X :: PSeries (ST s) (R Q) X_
a_1X = PS $ ll[toMPoly [(-4,[])], toMPoly [(-2,[])]]
a_0X :: PSeries (ST s) (R Q) X_
a_0X = PS $ ll[toMPoly [(3,[])], toMPoly [(6,[])]]
fXY :: F (ST s) (R Q) X_ Y_
fXY = UP [a_0X, a_1X, a_2X]

fY1 :: UPoly (R Q) Y_
fY1 = UP $ [toMPoly [(-1,[])],toMPoly[(1,[])]]
fY2 :: UPoly (R Q) Y_
fY2 = UP $ [toMPoly[(-3,[])],toMPoly [(1,[])]]


-- | the degree of a polynomial with power series coeff
ydeg :: (Monad m, CommutativeRing a) => F m a x y -> Int
ydeg (UP as) | length as > 0 = length as - 1
             | otherwise     = 0


-- | the Y projection of a polynomial F(X,Y) \in k[[X]][Y]. i.e. F(0,Y)
proj_y :: (Monad m, CommutativeRing a) => F m a x y -> UPoly a y
proj_y (UP as) = UP $ Lst.map hd as
             where hd (PS xs) = head xs

-- | the cannonical embedding (injective homomorphism) :  k[[X]][Y] -> k[Y][[X]]
phi :: (CommutativeRing a, Eq a, Monad m) => F m a x y -> E m a y x
phi (UP as) = PS $ phi' as

phi' :: (CommutativeRing a, Eq a, Monad m) => [PSeries m a x] -> Stream m (UPoly a y)
phi' as  = Cons (toUPoly $ Lst.map (head . fromPS) as) z'
            where z' = do as' <- mapM (tail . fromPS) as
                          return $ phi' (Lst.map toPS as')


-- | a homomorphism  (f : k[Y][[X]] and f bounded in Y) -> k [[X]] [Y].
-- generally the map k[Y][[X]] -> k [[X]] [Y] is not injective. but the partial map defined here is indeed injective
-- since any f in k[Y] [[X]] bounded in Y is equal to one in k [[X]][Y]
--and back
--the map is not surjective so this is not logically precise
--but since we pass the y_degree this should work fine
psi :: (CommutativeRing a, Eq a, Monad m) => Integer -> E m a y x -> F m a x y
psi deg p =  UP $ psi' (fromInteger deg) p 0

psi' :: (CommutativeRing a, Eq a, Monad m) => Int -> PSeries m (UPoly a y) x -> Int -> [PSeries m a x]
psi' deg bs n | n > deg   = []
              | otherwise =  h : t 
                  where h = toPS (map (hd' . fromUPoly) $ fromPS bs)
                        t = psi' deg (PS $ (map (toUPoly . tl' . fromUPoly) $ fromPS bs)) (n+1)
                        hd' [] = zero
                        hd' (a:xs) = a
                        tl' [] = []
                        tl' (a:xs) = xs

-- | Hensel's lemma
lemma :: (Field k, Eq k, Show k) => F (ST (S k)) (R k) x y -> UPoly (R k) y -> UPoly (R k) y -> ST (S k) (F (ST (S k)) (R k) x y, F (ST (S k)) (R k) x y)
lemma fXY g_0 h_0 = do z <- iszero ((g_0 <*> h_0) <-> proj_y fXY)  
                       case z of 
                        False -> error ("polynomial is not monic or factors aren't correct (" ++ show (fromUPoly g_0) ++ ")" ++ show (fromUPoly h_0))
                        True  -> do (hi , gi, gc, p, q) <- iGCD g_0 h_0
                                    (gc, gc_deg) <- iDeg gc 
                                    case gc_deg == 0 of 
                                     False -> error "factors are not coprime" 
                                     True  -> do let (gyx, hyx) = gYXhYX (phi fXY) g_0 h_0 gi hi
                                                 return (psi (deg g_0) gyx, psi (deg h_0) hyx)
--the two factors as power series
gYXhYX :: (Field k, Eq k, Show k) => E (ST (S k)) (R k) y x -> UPoly (R k) y -> UPoly (R k) y -> UPoly (R k) y -> UPoly (R k) y -> (E (ST (S k)) (R k) y x, E (ST (S k)) (R k) y x)
gYXhYX f g_0 h_0 gi hi = (PS $ Cons g_0 tlG, PS $ Cons h_0 tlH)
                    where tlG    = liftM fromPS $ fstM tlGtlH
                          tlH    = liftM fromPS $ sndM tlGtlH
                          tlGtlH = tlGH f g_0 h_0 gi hi [] []

--tails of the two power series factors
tlGH :: (Field k, Eq k, Show k) => E (ST (S k)) (R k) y x -> UPoly (R k) y -> UPoly (R k) y 
                                   -> UPoly (R k) y -> UPoly (R k) y 
                                   -> [UPoly (R k) y] -> [UPoly (R k) y]
                                   -> ST (S k) (E (ST (S k)) (R k) y x, E (ST (S k)) (R k) y x)

tlGH f g_0 h_0 gi hi gs hs = do tlF <- tl f
                                let uq = aux tlF gs hs
                                (e1,e2)  <- (hi <*> uq) `qr` h_0
                                let g = (gi <*> uq) <+> (g_0 <*> e1)
                                let h = e2
                                let tlgh = tlGH tlF g_0 h_0 gi hi (g:gs) (h:hs)
                                return (PS $ Cons g (liftM fromPS $ fstM tlgh), PS $ Cons h (liftM fromPS $ sndM tlgh))


--auxilary computation Uq = Fq - Sum_(i+j=q, i < q, j < q) Gi Hj 
aux :: (Field k, Eq k, Show k) => E (ST (S k)) (R k) y x -> [UPoly (R k) y] -> [UPoly (R k) y] -> UPoly (R k) y
aux f gs hs | length hs == length gs = hd f <-> gh
            | otherwise = error " gs hs lengths should be euqal !"
                where hsi = reverse hs
                      gh  = Lst.foldr (<+>) zero $ Lst.zipWith (<*>) gs hsi



--functions to help show the result of the lemma
run' :: (Field k, Eq k, Show k) => ST (S k) (F (ST (S k)) (R k) x y, F (ST (S k)) (R k) x y) 
                                      -> ST (S k) (UPoly (UPoly (R k) x) y, UPoly(UPoly (R k) x) y)
run' pltup = do (UP f1, UP f2) <- pltup
                mtup (UP) (mapM forshow f1, mapM forshow f2)


mtup :: (Monad m) => (a -> b) -> (m a, m a) -> m (b, b)
mtup f (mx,my) = do x <- mx
                    y <- my
                    return (f x, f y)


forshow :: (Monad m, CommutativeRing a, Eq a) => (PSeries m a x) -> m (UPoly a x)
forshow (PS xs) = liftM (toUPoly) $ liftM (head xs : ) $ liftM (Lst.map head) $ rep 6 (tail) xs
                



