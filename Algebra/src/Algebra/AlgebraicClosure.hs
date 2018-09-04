{-# LANGUAGE EmptyDataDecls, RelaxedPolyRec, TypeSynonymInstances, ScopedTypeVariables, FlexibleContexts #-}
module Algebra.AlgebraicClosure where
import Control.Arrow (second)
import Data.Function (on)
import Data.List (sortBy, permutations, union, groupBy,genericSplitAt, sort)
import Data.Map (Map, partitionWithKey, mapKeys)
import qualified Data.Map as Map
import Test.QuickCheck
import Algebra.Structures.Rings
import Algebra.Monomial
import Algebra.Q
import Algebra.MPoly
import qualified Algebra.UPoly as UPoly 
import Algebra.UPoly hiding (sqfrDec, sqfr)
import Algebra.TypeString.Char hiding (Q, R, S)


-- | The type of states
newtype ST s a = ST { runState :: s -> [(s,a)] }

-- | get extracts the state from the monad
get :: ST s s
get = ST $ \s-> [(s,s)]
-- | puts a state
put :: s -> ST s ()
put s = ST $ \_-> [(s,())]

-- | putUg puts both a state and a single value
putBoth :: s -> a -> ST s a
putBoth s a = ST $ \_-> [(s,a)]

-- | putD puts two states
putD :: s -> s -> ST s ()
putD s1 s2 = ST $ \_->[(s1,()), (s2,())]

-- | putDUg puts two states and two values
putDBoth :: s -> s -> a -> a -> ST s a
putDBoth s1 s2 q1 q2 = ST $ \_-> [(s1,q1),(s2,q2)]

-- | Applies the state type to a state. used to run the monad computation
apply :: ST s a -> s -> [(s,a)]
apply m s = runState m s 

-- | The monad type of states
instance Monad (ST s) where
  (ST p) >>= k = ST (\s0 -> let as = p s0 in
                              concatMap (\(st,vl) -> runState (k vl) st) as)
  return a = ST (\s -> [(s,a)])



-- | Len order of Monomials
data Len 
instance Order Len where
  comp (Mon xs) (Mon ys) | length xs' == length ys' =  compare (reverse xs') (reverse ys')
                         | otherwise = compare (length xs') (length ys')
                              where xs' = dropTail0 xs
                                    ys' = dropTail0 ys

-- | The type of multivariate polynomials ordered with Len ordering
-- This type is used to represent the algebraic closure of the base field k
type R k = MPoly k Len

-- | a helper method droping 0's from a list of integers
dropTail0 :: [Integer] -> [Integer]
dropTail0 = reverse . dropWhile (==0) . reverse

-- | the number of indeterminates in the polynomial 
ord' :: (Field k, Eq k) => R k -> Integer
ord' f = toInteger $ length m 
      where Mon m = lm f

-- | the number of indeterminates in the polynomial
upOrd' :: (Field k, Eq k) => UPoly (R k) x -> Integer
upOrd' f@(UP xs) | null xs = 1 
                 | otherwise = maximum (map ord' xs) + 1
-- | instance declaration of Ord R k
instance (Field k, Eq k) => Ord (R k) where
  compare a b | ord' a == ord' b = EQ
              | ord' a < ord' b = LT
              | otherwise       = GT


-- | takes a key and splits the map into a two 
splitLess :: Ord k => k -> Map k a -> (Map k a, Map k a)
splitLess k m = partitionWithKey (\k' _ -> k' < k) m

-- | takes alist of keys and splis the map into alist of maps recursively
-- returning alist where the ith map contains keys less than the ith key but greater than the (i+1)th key
splitList :: Ord k => [k] -> Map k a -> [Map k a]
splitList [] m = [m]
splitList (k:ks) m = m1 : splitList ks m2
                     where (m1,m2) = splitLess k m
-- | useful only with the Len order. If the greatest monomial is a X^i Y^j Z^k the key list returned 
-- is Z,...,Z^k
keyList :: Monomial ord -> [Monomial ord]
keyList (Mon xs)        | null ks = []
                        | n == 0       = error "keyList: last elem in monom is of 0 deg"
                        | otherwise    = triv (replicate (l-1) 0) (n) 1
                           where ks = dropTail0 (xs)
                                 n = toInteger $ last ks
                                 l = length ks
                                 triv ks n m | n < m = []
                                             | otherwise = (Mon $ ks ++ [m]) : triv ks n (m+1)
-- | Transform a multivariate polynomial in k[x1,...xn] to a univariate on in k[x1,...,xn-1][xn]
poly :: (CommutativeRing r, Eq r) =>  MPoly r Len -> UPoly (MPoly r Len) x
poly f@(M bb) | f==zero = UP []
              | otherwise = UP $ map (\m -> M $ mapKeys alterKey m) spL
            where
                keyL = keyList $ lm f
                spL = splitList keyL bb
                keyCr = Mon $ (\(Mon xs) -> replicate ((length xs) -1) 0 ++ [1]) (lm f)
                keyToCoef k = Mon (dropTail0 $ init $ (\(Mon k') -> k') k)
                alterKey k = if k > lm f then error "poly: weird key"
                                          else (if k >= keyCr then keyToCoef k else k)
                                                            


-- | the inverse of poly transform a univariate polynomial in k[x1,...,xn-1][xn] to multivariate on in k[x1,...xn]
-- note that isomorphism is not established due to manipulation on the monomials!!
mpoly :: (CommutativeRing r, Eq r) => Integer -> UPoly (MPoly r Len) x -> MPoly r Len
mpoly _ (UP []) = M Map.empty
mpoly n (UP xs) = toMPoly $ mpoly' xs (fromInteger $ n-1) 0

mpoly' [] _ _ = []
mpoly' (x:xs) n d | d == 0 = (toList x) ++ (mpoly' xs n (d+1))
                  | otherwise = map (\(v,m) -> (v, m++(replicate (n-(length m)) 0)++[d])) (toList x) ++ mpoly' xs n (d+1)
                                 where toList = (map (\(Mon a,b)-> (b,a))) . (Map.toList) . (\(M x) -> x)


-- | a state is a list of polynomials [R]
type S k = [R k]
-- | rank of state; namely the number of polynomials in the state
rank :: S k -> Integer
rank = toInteger . length

-- | inverse is the witness that R k is a field. an element x in a field is either invertible or is zero
-- i.e. either Left () or Right 1/x
inverse :: (Field k, Eq k) => R k -> ST (S k) (Either () (R k))
inverse i | (ord' i) == 0 = ST (\st -> [(st, if lc i == zero then Left () else Right $ toMPoly [(inv $ lc i,[])])])
          | otherwise     = do st <- get 
                               let n = ord' i
                               let m = rank st
                               case (n > m) of
                                 True -> error "inverse: element belong to superfield"
                                 _    -> do let mpoly' = mpoly n
                                            let p = poly (st !! fromInteger (n-1))
                                            let q = poly i
                                            (r,s,g',p',q') <- iGCD p q
                                            (g,g_deg)      <- iDeg g'
                                            (_,p_deg)      <- iDeg p
                                            case g_deg > 0 of
                                              True  -> case g_deg == p_deg of
                                                         False -> do updateState n $ mpoly' g
                                                                     s1 <- get
                                                                     put st
                                                                     updateState n $ mpoly' p'
                                                                     s2 <- get
                                                                     (e,_,y,_,_) <- iGCD g p' --y should always constant
                                                                     Right yinv <- inverse $ mpoly' y
                                                                     let t = (mpoly' e) <*> (yinv) <*> (mpoly' s)
                                                                     tmod <- modPrevState t
                                                                     putDBoth s1 s2 (Left ()) (Right tmod)
                                                                     --return $ Left ()
                                                         True -> return $ Left ()
                                              False -> do Right ginv <- inverse $ mpoly' g
                                                          t <- modPrevState $ (mpoly' s) <*> ginv
                                                          return $ Right $ t

-- | revert reverts to a previous state of rank n
revertState :: (Field k, Eq k) => Integer -> ST (S k) ()
revertState n = do st <- get
                   case (rank st < n) of
                    True  -> error "revertState: current state rank is less than required state"
                    False -> put $ take (fromInteger n) st
-- | appendToState
appendToState :: (Field k, Eq k) => R k -> ST (S k) ()
appendToState s = do st   <- get 
                     lcsInv <- inverse $ (last $ fromUPoly $ poly s)
                     case lcsInv of
                      Right x -> do let sMonic = x <*> s
                                    smod <- modPrevState sMonic
                                    put $ st ++ [smod]
                      _  -> error "appendToState: leading coefficient state not invertible!"
                     
                      
                     
-- | updateState 
updateState :: (Field k, Eq k) => Integer -> R k -> ST (S k) ()
updateState n s = do st <- get --get the current state
                     case (rank st < n) of
                      True  -> error "current state rank is less than the update index"
                      False -> do let (st1,st2) = splitAt (fromInteger n) st --splitting the state
                                  revertState (n-1) --reverting to state of rank n-1
                                  appendToState s
                                  mapM_ appendToState st2 --appending the rest of the states
-- | moulo previous state
modPrevState :: (Field k, Eq k) => R k -> ST (S k) (R k)
modPrevState r = do let n = ord' r
                    let mpoly' = mpoly n
                    let (UP ps) = poly r
                    st <- get
                    let ps' = map (modState st) ps
                    let r' = (UP ps')
                    return $ (mpoly' r')


-- | modulo the current state state
modState :: (Field k, Eq k) => S k -> R k -> R k
modState st r | n == 0 = r
              | otherwise = mpoly' (UP rs')
          where n = ord' r
                mpoly' = mpoly n
                s = st !! (fromInteger n-1)
                r' = poly r
                (_,UP rs) = euclid r' (poly s)
                rs' = map (modState st) rs

-- | simple division based on the inverse function
(/^) :: (Field k, Eq k) => R k -> R k -> ST (S k) (Either () (R k))
r1 /^ r2 = do _ <- get
              r2Inv <- inverse r2
              case r2Inv of 
                    Left () -> return $ Left () 
                    Right r2Inv' -> return $ Right $ r1 <*> r2Inv'

-- | division of a polynomial over the algebraic closure of k by an element in k (deterministic -no branching)
divByBase :: (Field k, Eq k) => R k -> k -> (R k)
divByBase  (M m)   r2 = M $ Map.map (</>r2) m

--a type for quintuples just for bervity
type Quint a = (a,a,a,a,a) 
--maps over quintuples
mapQ :: (a -> b) -> Quint a -> Quint b
mapQ f q = (\(a1,a2,a3,a4,a5) -> (f a1, f a2, f a3, f a4, f a5)) q
--abbrev for tuples
type Tup a = (a,a)

-- | quotient remainder, cheaper than gcd
qr :: (Field k, Eq k) => UPoly (R k) x -> UPoly (R k) x -> ST (S k) (UPoly (R k) x, UPoly (R k) x)
qr p q = do (ps,p_deg) <- iDeg p
            (qs,q_deg) <- iDeg q
            case qs of 
             (UP []) -> return (zero, ps)
             _       -> do case (p_deg < q_deg) of 
                            True  -> return (zero, ps)
                            False ->  do Right invLtQs <- inverse $ UPoly.lt qs
                                         let t  = UPoly.lt ps <*> invLtQs
                                         let l  = fromInteger $ p_deg - q_deg
                                         let t' = UP $ replicate l zero ++ [t]
                                         let q2  = t' <*> qs
                                         (quo, rem) <- qr (ps <-> q2) qs
                                         return $ (t' <+> quo, rem)
                           
-- | modulo
modulo p q = do (qu,rm) <- qr p q
                return $ rm
-- | quotient 
quotient p q = do (qu,rm) <- qr p q
                  return $ qu 
-- | intelligent gcd given two polynomials p q produces a quintuple (r,s,g,p',q') such that
--   r p + s q = g , p' g = p, and q' g = q
iGCD :: (Field k, Eq k) => UPoly (R k) x -> UPoly (R k) x -> ST (S k) (Quint (UPoly (R k) x))
iGCD p q = do (r,s,g,neg_q',p') <- iGCD' p q (one, zero) (zero, one)
              (g, g_deg)        <- iDeg g
              case g_deg of
               0 -> do case g of
                        (UP []) -> return $ (r,s,g, p', neg neg_q')
                        (UP [e]) -> do Right eInv <- inverse e
                                       return $ (r <*> (UP [eInv]), s <*> (UP [eInv]), one, p'<*> g, g <*> neg neg_q')
               _ -> return $ (r,s,g,p',neg neg_q')


-- | the actual computation of the iGCD occurs here except that this one produces
-- (r,s,g,-q',p') such that r p + s q = g, p' g = p, q' g = q

iGCD' :: (Field k, Eq k) => UPoly (R k) x -> UPoly (R k) x -> Tup (UPoly (R k) x) -> Tup (UPoly (R k) x) -> ST (S k) (Quint (UPoly (R k) x))
iGCD' p q (r,s) (q',p') = do (qs, q_deg) <- iDeg q
                             case qs of
                               (UP []) -> return $ (r,s,p,q',p')
                               _       -> do (ps, p_deg) <- iDeg p 
                                             case ps of
                                              (UP []) -> return $ (q',p',q,r,s)
                                              _    -> do case p_deg < q_deg of
                                                          True  -> iGCD' qs ps (q',p') (r,s)
                                                          False -> do Right invLtQs <- inverse $ UPoly.lt qs
                                                                      let t  = UPoly.lt ps <*> invLtQs
                                                                      let l  = fromInteger $ p_deg - q_deg
                                                                      let t' = UP $ replicate l zero ++ [t]
                                                                      let (q2,q2',p2') = (t' <*> qs, t' <*> q', t' <*> p')
                                                                      iGCD' (ps <-> q2) qs (r <-> q2', s <-> p2') (q',p') 

iDeg :: (Field k, Eq k) => UPoly (R k) x -> ST (S k) (UPoly (R k) x, Integer)
iDeg p@(UP xs) = do st <- get 
                    let ps' = toUPoly $ map (modState st) xs
                    return (ps', deg ps')

-- | computes the degree of a polynomial, returning both the degree and a modified polynomial
siDeg :: (Field k, Eq k) => UPoly (R k) x -> ST (S k) (UPoly (R k) x, Integer)
siDeg p@(UP xs) = do case xs of
                      []   -> return (p, 0)
                      x:[] -> do ltInv <- inverse $ x
                                 case ltInv of
                                  Left () -> return (UP [], 0)
                                  _       -> return (p, 0)
                      _    -> do ltInv <- inverse $ UPoly.lt p
                                 case ltInv of
                                  Left () -> iDeg (UP $ init xs)
                                  Right _ -> return (p, toInteger (length xs - 1))

-- | test if a polynomial is zero
iszerop :: (Field k, Eq k) => UPoly (R k) x -> ST (S k) Bool
iszerop g = do case g of 
                UP []     -> return $ True 
                UP (x:xs) -> do testInv <- inverse $ UPoly.lt g
                                case testInv of
                                  Left () -> iszerop (UP $ init (x:xs))
                                  Right _ -> return $ False

isZero :: (Field k, Eq k) => R k-> ST (S k) Bool
isZero g = do testInv <- inverse g
              case testInv of
               Left () -> return True
               Right _ -> return  False
--should be moved to AlgebraicClosure 
isUnit :: (Field k, Eq k, Show k) => R k -> ST (S k) Bool
isUnit  r = do rInv <- inverse r
               case rInv of 
                Right _ -> return True
                Left () -> return False

-- | isSqFr test for square freeness 
isSqFr :: (Num k, Field k, Eq k) => UPoly (R k) x -> ST (S k) Bool
isSqFr f = do let f' = deriv f
              (_,_,g,_,_) <- iGCD f f'
              (g,g_deg) <- iDeg g
              case g_deg of 
               0 -> return True
               _ -> return False 
-- |monadic square free associate of f 
-- Teo Mora; Solving Polynomial Equations Systems I. pg 69-70
sqfr :: (Num k, Field k, Eq k) => UPoly (R k) x -> ST (S k) (UPoly (R k) x)
sqfr f = do let f' = deriv f
            (_,_,_,d,_) <- iGCD f f'
            return d


-- | monadic distinct power factorization aka square free decomposition 
-- Teo Mora; Solving Polynomial Equations Systems I. pg 69-70
sqfrDec :: (Num k, Field k) => UPoly (R k) x -> ST (S k) [UPoly (R k) x]
sqfrDec f = do (r,s,g,p,q) <- iGCD f (deriv f)
               sqfrDec' g p
sqfrDec' :: (Num k, Field k) => UPoly (R k) x -> UPoly (R k) x -> ST (S k) [UPoly (R k) x]
sqfrDec' p q = do (_,_,s,d,t) <- iGCD p q
                  (_, s_deg)   <- iDeg s
                  case s_deg > 0 of 
                    True  -> do l <- sqfrDec' d s
                                return $ t : l
                    False -> return $ [t]

-- | root
-- function, a witnes that R k is algebraicly closed. given a monic polynomial returns a root of the polynomial
root :: (Num k, Field k, Eq k) => UPoly (R k) x -> ST (S k) (R k)
root p = do st <- get
            let m = rank st
            let n = upOrd' p
            case m < n - 1 of
              True  -> error "root: polynomial is over a super field"
              False -> do let p' = poly $ mpoly (m+1) p --converting to a polynomial in the right indeterminate
                          q <- sqfr p' -- the square free fucks up the monoticity of the polynomail
                          let s = mpoly (m+1) q
                          let r  = toMPoly [(one, replicate (fromInteger m) 0 ++ [1])]
                          monicS <- monic $ poly s
                          --if (not monicS) then error $ "root: "++ show (fromUPoly $ poly s, fromUPoly q) else do
                          appendToState s
                          return $ r

-- | monic
-- test monticity of polynomial over the algebraically closed field
monic f = do (UP p, n) <- iDeg f
             if (p == []) then return False else do
             d <- inverse $ last p <-> one
             case d of 
              Left () -> return True
              _       -> return False

ex p = do alpha <- root p
          beta  <- root p
          inverse $ alpha - beta
ex2 p = do r <- root p
           let d = UP [(zero <-> r),one]
           qr p d
ex3 p = do r <- root p
           return $ UP [(zero <-> r),one]
           
