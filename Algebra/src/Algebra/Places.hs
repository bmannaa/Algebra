module Algebra.Places where
import Algebra.AlgebraicClosure
import Algebra.UPoly hiding (substitute)
import qualified Algebra.UPoly as Up
import Algebra.MPoly hiding (dropZeros)
import Algebra.Structures.Rings
import Data.List hiding (lookup)
import Prelude hiding ((^^),lookup)
import Algebra.TypeString.Char hiding (Q, R, S)
import Algebra.Q
import Algebra.TwoVariatePoly
import Algebra.Structures.FieldOfFractions

--print intermediate results
-- the transformation x' --> x, y' --> y is invertible, (x,y) |---->(f(x,y), g(x,y)) are automorphisms of L\k = k(x,y)
place:: (Field k, Num k) => TwoVarPoly (R k) x y -> ST (S k) [(FieldOfFractions (TwoVarPoly (R k) x y), FieldOfFractions(TwoVarPoly (R k) x y))]
place f@(TVP p) = do f2 <- mFilter (\((_,_),x) -> isUnit x) p
                     let (z1,z2) = (lookup (0,1) f2, lookup (1,0) f2)
                     case (z1,z2) of
                        (Nothing,Nothing) -> do let homComps = tvpHomogenousDec $ TVP f2
                                                let f3 = head homComps 
                                                let mltplcty = (\((a,b),_) -> a+b) $ head $ tvpToLst f3
                                                case (lookup (0,mltplcty) $ tvpToLst f3) of
                                                  Nothing -> do ll <-fun1 f2 f3 mltplcty
                                                                rr <- fun2 f2 mltplcty
                                                                return $ ll ++ rr
                                                  Just a  -> fun1 f2 f3 mltplcty
                                                                
                        _                 -> do return [(toFieldOfFractions $ TVP [((1,0),one)], toFieldOfFractions $ TVP [((0,1),one)])]
           where fun1 f2 f3 mltplcty= 
                              do let f4 = map (\((_,a),b) -> ((0,a),b)) $ tvpToLst f3 
                                 let f5 = collect f4
                                 let f6 = map (\((_,a),b)->(a,b)) f5
                                 let f7 = UP $ ylk $ yle f6
                                 r <- root f7
                                 --y=x(y'+r)
                                 let y = TVP [((1,1),one), ((1,0),r)]
                                 let x = TVP [((1,0),one)]
                                 let f8 = advSubstitute (\r -> TVP[((0,0),r)]) x y (TVP f2)
                                 let f9 = map (\((a,b),c) ->((a-mltplcty,b),c)) $ tvpToLst f8
                                 --y'= (y - xr)/x
                                 let y' = F (TVP [((0,1),one), ((1,0),neg r)],TVP [((1,0),one)])
                                 let x' = F(TVP[((1,0),one)],one)
                                 --(a',b') <- place $ TVP f9
                                 pls <- place $ TVP f9
                                 return [(changeVar a' x' y', changeVar b' x' y') | (a',b') <- pls]
                 fun2 f2 mltplcty = 
                           do let x' = F (TVP[((1,0),one)], TVP[((0,1),one)]) --x'=x/y
                              let y' = F (TVP[((0,1),one)], one) --y'=y
                              let f4 = map (\((a,b),c) ->((a,a+b-mltplcty),c)) f2 
                              let f5 = TVP $ collect f4
                              --(a',b') <- place f5
                              pls <- place f5
                              return [(changeVar a' x' y', changeVar b' x' y') | (a',b') <-pls]

places :: (Field k, Num k) => R k -> R k -> TwoVarPoly (R k) x y 
                                  -> ST (S k) [(FieldOfFractions (TwoVarPoly (R k) x y), FieldOfFractions(TwoVarPoly (R k) x y))]
places a b f = do ztst <- isZero $ substitute a b f
                  if (not ztst) then error "places: f(a,b) must be zero" else do
                  let x = TVP [((1,0),one),((0,0),a)] -- x = x' + a
                  let x' = toFieldOfFractions $ TVP [((1,0),one), ((0,0), neg a)]
                  let y = TVP [((0,1),one),((0,0),b)] -- y = y' + b
                  let y' = toFieldOfFractions $ TVP [((0,1),one), ((0,0), neg b)]
                  --(px', py') <- place $ advSubstitute (\r -> TVP [((0,0),r)] ) x y f
                  pls <- place $ advSubstitute (\r -> TVP [((0,0),r)] ) x y f
                  return [(changeVar px' x' y', changeVar py' x' y') | (px',py') <- pls]

--compute places at (0,0)
--keep change of variables
-- result x^(n) = \phi(x,y)

findZeros :: (Field k, Num k) => UPoly (R k) x -> UPoly (UPoly (R k) x) y -> ST (S k) (R k, R k)
findZeros g f = do r1 <- root g
                   let f1 = UP $ map (Up.substitute r1) $ fromUPoly f
                   r2 <- root f1
                   return (r1,r2)




putAtOrigin :: (CommutativeRing r, Eq r) => (r,r) -> TwoVarPoly r x y-> TwoVarPoly r x y
putAtOrigin (a,b) (TVP ps) = TVP ls'
          where
           ls =  groupBy xly $ sortBy xty (concatMap (f (neg a, neg b)) ps)
           ls' = map(\xs -> (fst $ head xs, foldr (\x y -> snd x <+> y) zero xs)) ls


ylt :: Ord a => (a,b) -> (a,c) -> Ordering
ylt (a1,_) (a2,_) = compare a1 a2

yeq :: (Eq a) => (a,b) -> (a,c) -> Bool
yeq (a1,_) (a2,_) = a1==a2

compSumXY :: ((Int,Int),b) -> ((Int,Int),c) -> Ordering
compSumXY ((a,b),_) ((c,d),_) = compare (a+b) (c+d)

f :: (CommutativeRing r, Eq r) => (r,r) -> ((Int, Int),r) -> [((Int,Int),r)]
f (a,b) ((p1,p2), r) = ds
         where
           xs = (\(UP x) -> x) $ (UP [a,one])^^p1
           xs' = zip [0..] xs 
           ys = (\(UP x) -> x) $ (UP [b,one])^^p2
           ys' = zip [0..] ys
           ds = [((a,c), b <*> d <*> r) | (a,b)<-xs', (c,d)<-ys']
           n = deg (UP xs) + deg (UP ys) + 1




mFilter :: (Monad m) => (a -> m Bool) -> [a] -> m [a]
mFilter _ [] = return []
mFilter f (a:as) = do b <- f a
                      bs <- mFilter f as
                      if b then return (a:bs) else return bs

lookup :: (Eq a, Ord a) => (a,a)-> [((a,a),b)] -> Maybe b
lookup _ [] = Nothing
lookup d ((d',b):xs) | d==d' = Just b
                     | otherwise = lookup d xs




polyF :: UPoly (UPoly Q X_) Y_
polyF=UP [UP [0,1,2,3],UP [1,2,3,4], UP [2,3,4,5],UP [3,4,5,6],UP [4,5,6,7],UP [5,6,7,8]]

polyT :: UPoly (UPoly Q X_) Y_
polyT=UP [UP [0,1,2],UP [1,0,0,2], UP [1]]

polyV= [[0,1,2,3],[1,2,3,4], [2,3,4,5],[3,4,5,6],[4,5,6,7],[5,6,7,8]]

tvp0 ::TwoVarPoly Q X_ Y_
tvp0 = TVP [((0,2),1), ((0,0),-1),((4,0),1)]
--x3+y3 =xy
tvp1::TwoVarPoly Q X_ Y_
tvp1= TVP [((1,1),-1), ((0,3),1),((3,0),1)]
gx :: UPoly Q X_
gx = UP [0,1]

tvp2::TwoVarPoly Q X_ Y_
tvp2= TVP [((3,0),1), ((2,0),-1), ((0,3),1)]

tvp3::TwoVarPoly Q X_ Y_
tvp3= TVP [((2,2),-4), ((0,6),1),((6,0),1), ((2,4),3), ((4,2),3)]

tvp4::TwoVarPoly Q X_ Y_
tvp4= TVP [((3,0),1), ((0,3),1),((1,1),-1)]

tvp5::TwoVarPoly Q X_ Y_
tvp5 =TVP [((4,0),1), ((0,4),1),((2,1),1),((1,2),-1)]

fol::TwoVarPoly Q X_ Y_

fol =TVP [((4,0),1), ((2,2),2),((0,4),1),((2,0),-2), ((0,2),-2), ((1,1),-4)]

tvp6 :: TwoVarPoly Q X_ Y_
tvp6 =TVP [((0,16),1), ((6,12),-4),((8,11),-4),((10,10),1),((12,8),6),((14,7),8),((16,6),14),((18,5),4),((20,4),1),((18,4),-4),((20,3),-4),((22,2),1),((24,0),1)]

tvp7 :: TwoVarPoly Q X_ Y_
tvp7 =TVP [((0,8),1), ((3,3),-4),((2,2),-4),((8,0),1)]

tvp8 :: TwoVarPoly Q X_ Y_
tvp8 = TVP [((0,6),1), ((6,0),1), ((2,4),3), ((4,2),3), ((2,2),-4)]
embedp :: (CommutativeRing r, Eq r) => UPoly r x -> UPoly (R r) x
embedp (UP p) = UP $ map (\y -> toMPoly [(y,[])]) p 

embedtvp :: (CommutativeRing r, Eq r) => TwoVarPoly r x y -> TwoVarPoly (R r) x y
embedtvp (TVP p) = TVP $ map (\((a,b),y) -> ((a,b),toMPoly [(y,[])])) p 