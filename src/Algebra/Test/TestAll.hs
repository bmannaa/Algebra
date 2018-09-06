{-# LANGUAGE OverlappingInstances #-}
module Algebra.Test.TestAll where

-- Import EVERYTHING in order to check that nothing is wrong
import Algebra.Structures.Rings
import qualified Algebra.Structures.Groups as G
import Algebra.Structures.BezoutDomains
import Algebra.Structures.EuclideanDomains
import Algebra.Structures.PruferDomains
import Algebra.Structures.StronglyDiscrete
import Algebra.Structures.Coherent
import Algebra.Structures.GCDDomains
import Algebra.Structures.FieldOfFractions

import Algebra.TypeString.Char hiding (Q,Z)

import Algebra.HenselLemma
-- import Algebra.FormalPowerSeries
import Algebra.FieldOfRationalFunctions
import Algebra.Ideals
import Algebra.PLM
import Algebra.Matrix
import Algebra.Q
import qualified Algebra.UPoly as UP
import Algebra.Monomial
import qualified Algebra.MPoly as MP
import Algebra.Z
import Algebra.Zn
import Algebra.ZSqrt5
import Algebra.EllipticCurve

import Algebra.Examples.Zn_Examples

import Test.QuickCheck

-- Properties:

-----------------------------------------------------------------------------
{- Z

-- Properties that it satisfies:
 o Integral domain
 o Euclidean domain
 o Prüfer domain
 o Bezout domain
 o GCD domain
 o Intersection from Bezout domains
 o Intersection from Prüfer domains
 o PLM for Bezout domains
 o PLM for Prüfer domains
 o calcUVWT
 o Coherence from Bezout domains
 o Coherence from Prüfer domains
 o Solve MxN
 o Strongly Discrete
 o Solve general equation, Ax=b

-- Properties that it should satisfy:

-}

propIntDomInt, propEuclidDomInt, propPruferDomInt :: Z -> Z -> Z -> Property
propIntDomInt    = propIntegralDomain
propEuclidDomInt = propEuclideanDomain
propPruferDomInt = propPruferDomain

propBezoutDomainInt :: Ideal Z -> Z -> Z -> Z -> Property
propBezoutDomainInt = propBezoutDomain

propGCDDomInt :: Z -> Z -> Z -> Property
propGCDDomInt = propGCDDomain

-- Intersection from Bezout and Prüfer domains
propIntersectionBInt :: Ideal Z -> Ideal Z -> Bool
propIntersectionBInt = isSameIdeal intersectionB 

propIntersectionPInt :: Ideal Z -> Ideal Z -> Property
propIntersectionPInt i@(Id is) j@(Id js) = 
  length is <= 10 && length js <= 10 ==> isSameIdeal intersectionP i j

-- Use the function for computing PLM for Bezout domains
propPLMBInt :: Ideal Z -> Bool
propPLMBInt id = propPLM id (computePLM_B id)

propCalcUVWTInt :: Z -> Z -> Property
propCalcUVWTInt a b = propCalcUVWT a b

-- Use the function for computing PLM for Prufer domains
propPLMPDInt :: Ideal Z -> Bool
propPLMPDInt id = propPLM id (computePLM_PD id)

-- Using coherence from Bezout domains
propCoherentInt :: Vector Z -> Bool
propCoherentInt m = isSolution (vectorToMatrix m ) (solveB m)

-- Using coherence from Prüfer domains
propCoherentPDInt :: Vector Z -> Bool
propCoherentPDInt m = isSolution (vectorToMatrix m) (solvePD m)

-- propSolveMxNInt :: Matrix Z -> Bool
-- propSolveMxNInt = propSolveMxN

-- Properties for strongly discrete:
propStronglyDiscreteInt :: Z -> Ideal Z -> Bool
propStronglyDiscreteInt = propStronglyDiscrete

-- propSolveGeneralEquationInt :: Vector Z -> Z -> Bool
-- propSolveGeneralEquationInt = propSolveGeneralEquation

-- propSolveGeneralInt :: Matrix Z -> Vector Z -> Property 
-- propSolveGeneralInt = propSolveGeneral


-----------------------------------------------------------------------------
{- Z3

-- Properties that it satisfies:
 o Integral domain

-- Properties that it maybe should satisfy:
 o Coherence?
 o Solve MxN

-}

intDomZ3 :: Z3 -> Z3 -> Z3 -> Property
intDomZ3 = propIntegralDomain

-----------------------------------------------------------------------------
{- Z6

-- Properties that it satisfies:
 o Abelian group
 o Commutative Ring

-- Properties that it maybe should satisfy:
 o Coherence?
 o Solve MxN

-}

abelGroupZ6, commRingZ6 :: Z6 -> Z6 -> Z6 -> Property
abelGroupZ6 = G.propAbelianGroup
commRingZ6  = propCommRing :: Z6 -> Z6 -> Z6 -> Property

-----------------------------------------------------------------------------
{- Q

-- Properties that it satisfies:
 o Field

-- Properties that it maybe should satisfy:
 o Prüfer domain
 o Bezout domain
 o PLM for Bezout domains
 o PLM for Prüfer domains
 o Coherence from Bezout domains
 o Solve MxN
 o Coherence from Prüfer domains
 o Coherence from somewhere else?

-}

propFieldQ :: Q -> Q -> Q -> Property
propFieldQ = propField

-----------------------------------------------------------------------------
{- Q[x]

-- Properties that it satisfies:
 o Integral domain
 o Euclidean domain
 o Bezout domain
 o GCD domain
 o PLM for Bezout domains
 o Coherence from Bezout domains
 o Prüfer domain
 o PLM for Prüfer domains
 o Coherence from Prüfer domains
 o Solve MxN

-- Properties that it should satisfy:

-}

type Qx = UP.Qx

propIntDomPQx :: Qx -> Qx -> Qx -> Property
propIntDomPQx = propIntegralDomain

propEuclidDomPQx :: Qx -> Qx -> Qx -> Property
propEuclidDomPQx = propEuclideanDomain

-- Bezout domain properties:

propBezoutDomainPQx :: Ideal Qx -> Qx -> Qx -> Qx -> Property
propBezoutDomainPQx = propBezoutDomain

propGCDDomPQx :: Qx -> Qx -> Qx -> Property
propGCDDomPQx = propGCDDomain

propPLMBQx :: Ideal Qx -> Bool
propPLMBQx id = propPLM id (computePLM_B id)

propCoherentBQx :: Vector Qx -> Bool
propCoherentBQx m = isSolution (vectorToMatrix m) (solveB m)

-- Prüfer domain properties:

propPruferDomPQx :: Qx -> Qx -> Qx -> Property
propPruferDomPQx a b c = d a < 10 && d b < 10 && d c < 10 ==> propPruferDomain a b c

propPLMPDQx :: Ideal Qx -> Bool
propPLMPDQx id = propPLM id (computePLM_PD id)

-- Coherence from Prüfer domains. Tests only on ideals of length max 3 for speed.
propCoherentPPQx :: Vector Qx -> Property
propCoherentPPQx m = length (unVec m) <= 3 ==> case vectorToMatrix m `mul` solvePD m of
  M xs -> all (==zero) (concatMap unVec xs)

-- propSolveMxNPQx :: Matrix Qx -> Bool
-- propSolveMxNPQx = propSolveMxN

-- Properties for strongly discrete:
propStronglyDiscretePQx :: Qx -> Ideal Qx -> Bool
propStronglyDiscretePQx = propStronglyDiscrete

-- propSolveGeneralEquationPQx :: Vector Qx -> Qx -> Bool
-- propSolveGeneralEquationPQx = propSolveGeneralEquation

-----------------------------------------------------------------------------
{- Q[x1..xn]

-- Properties that it satisfies:
 o Integral domain
    - Lex
    - GrLex
    - GRevLex
 o Division
    - Lex
    - GrLex
    - GRevLex
 o Coherence 
 o Strongly discrete

-- Properties that it should satisfy:
 o Solve MxN

-}

propIntDomMPLex :: MP.MPoly Q Lex -> MP.MPoly Q Lex -> MP.MPoly Q Lex -> Property
propIntDomMPLex = propIntegralDomain 

propIntDomMPGrLex :: MP.MPoly Q GrLex -> MP.MPoly Q GrLex -> MP.MPoly Q GrLex -> Property
propIntDomMPGrLex = propIntegralDomain

propIntDomMPGRevLex :: MP.MPoly Q GRevLex -> MP.MPoly Q GRevLex -> MP.MPoly Q GRevLex -> Property
propIntDomMPGRevLex = propIntegralDomain

-- Division:
propDivideMPLex :: MP.MPoly Q Lex -> [MP.MPoly Q Lex] -> Bool
propDivideMPLex = MP.propDivideMPoly

propDivideMPGrLex :: MP.MPoly Q GrLex -> [MP.MPoly Q GrLex] -> Bool
propDivideMPGrLex = MP.propDivideMPoly

propDivideMPGRevLex :: MP.MPoly Q GRevLex -> [MP.MPoly Q GRevLex] -> Bool
propDivideMPGRevLex = MP.propDivideMPoly

-- Gröbner basis test:
propGbWitnessMPLex :: Ideal (MP.MPoly Q Lex) -> Property
propGbWitnessMPLex m = 
  all (\x -> (\(Mon xs) -> sum xs <= 10) (MP.lm x)) (fromId m) ==> MP.propGbWitness m

-- This give a compilation error which is really wierd...
-- propCoherentMPLex :: Vector (MP.MPoly Q Lex) -> Bool
-- propCoherentMPLex = propCoherent

propCoherentMPLex :: Vector (MP.MPoly Q Lex) -> Property
propCoherentMPLex m = all (\x -> (\(Mon xs) -> sum xs <= 10) (MP.lm x)) (unVec m) ==> 
  case vectorToMatrix m `mul` solveWithIntersection m MP.intersectionMP of
    M xs -> all (==zero) (concatMap unVec xs)

propStronglyDiscreteMPLex :: MP.MPoly Q Lex -> Ideal (MP.MPoly Q Lex) -> Bool
propStronglyDiscreteMPLex = propStronglyDiscrete
