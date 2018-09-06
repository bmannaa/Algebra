-------------------------------------------------------------------------------
-- Abstract algebra library 
-- 
-- Anders Mörtberg    <mortberg@student.chalmers.se>
-- Bassel Mannaa      <mannaa@student.chalmers.se>
--
-- Abstract:
-- This is a library written as part of our master theses. It focuses mainly on 
-- commutative algebra and coherent rings.
--
-- References:
--
-------------------------------------------------------------------------------

module README where

-------------------------------------------------------------------------------
-- Modules for representating different algebraic structures:

-- Representation of groups.
import Algebra.Structures.Groups

-- Representation of rings, commutative rings, integral domains and fields. 
import Algebra.Structures.Rings

-- Representation of strongly discrete rings which are rings in which ideal 
-- membership is decidable. 
import Algebra.Structures.StronglyDiscrete

-- Representation of coherent rings which are rings in which it is possible to
-- solve (homogenous) equations. We can solve AX=0 where A is a row vector. 
-- 
-- This module has three main proofs:
--  o If the intersection of two f.g. ideals is f.g. then the ring is coherent.
--  o If the ring is coherent we can solve systems of equations (A matrix).
--  o If the ring also is strongly discrete we can solve arbitrary systems (AX=B).
import Algebra.Structures.Coherent

-- Representation of Euclidean Domains with algorithms for computing generalized
-- gcd and extended Euclidean algorithm. There is also a proof that Euclidean 
-- domains are Prüfer domains. 
import Algebra.Structures.EuclideanDomains

-- Representation of Bezout domains which are integral domains where every 
-- finitely generated ideal is principal. The module has proof that Euclidean
-- domains are Bezout domains and that Bezout domains are coherent and Prüfer
-- domains.
import Algebra.Structures.BezoutDomains

-- Representation of GCD domains which are domains in which every pair of 
-- non-zero elements has a greatest common divisor. This contains a proof
-- that Bezout domains are GCD domains. This structure is useful for defining
-- fields of fractions where the quotients are reduced.
import Algebra.Structures.GCDDomains

-- Representation of Prüfer domains which are non-Noetherian analogues of 
-- Dedekind domains. This has a proof that Prüfer domains are coherent. 
import Algebra.Structures.PruferDomains

-- The contruction of a field of fraction for a GCD domain. The reason that this
-- is specialised for GCD domains is that the quotients should be reduced.
import Algebra.Structures.FieldOfFractions

-------------------------------------------------------------------------------
-- Some useful libraries:

-- Finitely generated ideals in commutative rings. 
import Algebra.Ideals

-- Small matrix library.
import Algebra.Matrix

-- Specification of principal localization matrices used in the coherence proof
-- for Prüfer domains.
import Algebra.PLM

-- Representation of all upper and lower case letters at the type-level. Used
-- for representing variable names for univariate polynomials.
import Algebra.TypeString.Char

-------------------------------------------------------------------------------
-- Concrete instances of the structures:

-- Z - The integers.
import Algebra.Z

-- Zn - The integers modulo n.
import Algebra.Zn

-- The ring Z[Sqrt(-5)]. That is Z adjoined with sqrt(-5).
import Algebra.ZSqrt5

-- Q - The rational numbers represented as the field of fractions of Z. 
import Algebra.Q

-- UPoly - Univariate polynomials over a commutative ring.
import Algebra.UPoly

-- The field of rational functions over k[x].
import Algebra.FieldOfRationalFunctions

-- The elliptic curve y^2=1-x^4 in k[x,y] with proof that it is a Prufer domain.
import Algebra.EllipticCurve

-- Monomials - Monomials indexed by their ordering.
import Algebra.Monomial

-- MPoly - Multivariate polynomials over a commutative ring.
import Algebra.MPoly

-- Formal Power Series over a commutative ring.
import Algebra.FormalPowerSeries

-------------------------------------------------------------------------------
-- Proofs using the library:

-- Proof of the Hensel lemma.
import Algebra.HenselLemma

-- Proof of Newton-Puiseux Theoem.
import Algebra.NewtonTheorem
