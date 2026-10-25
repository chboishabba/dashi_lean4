import Integration.EisensteinJZeroHeckeLocalAgreementExact
import Integration.EisensteinJZeroBadPrimeLocalFactorExact

/-!
# Finite Euler-product agreement for the j=0 CM curve

Prime-by-prime local agreement is already paid.  This file performs the first
genuinely global composition without adding any analytic assumption: for every
finite set of rational primes, the product of the elliptic local denominator
polynomials equals the product assembled from the conductor-normalized finite
ideal character.

This is deliberately a FINITE product theorem.  Passing to an infinite Euler
product, proving convergence, and identifying analytic L-functions are kept as
separate analytic obligations.
-/

namespace Integration.EisensteinJZeroFiniteEulerProductExact

open scoped BigOperators
open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroBadPrimeLocalFactorExact
open Integration.EisensteinJZeroHeckeLocalAgreementExact

/-- Rational primes as a proof-carrying type, avoiding hidden primality
assumptions inside finite products. -/
abbrev RationalPrime := {p : Nat // p.Prime}

private def goodPrime_gt_three (p : RationalPrime)
    (h2 : p.1 ≠ 2) (h3 : p.1 ≠ 3) : 3 < p.1 := by
  have hp2 := p.2.two_le
  omega

/-- Elliptic local denominator polynomial on the exact same curve, now at every
rational prime and scalar-extended to `EisensteinQA`. -/
noncomputable def ellipticPrimeEulerPolynomial
    (p : RationalPrime) (T : EisensteinQA) : EisensteinQA := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  if h2 : p.1 = 2 then
    exact 1
  else if h3 : p.1 = 3 then
    exact 1
  else
    exact ellipticGoodPrimeEulerPolynomialEisenstein p.1
      (goodPrime_gt_three p h2 h3) T

/-- Hecke-side rational-prime denominator.  Conductor primes contribute one;
good primes use the already-proved split/inert prime-ideal product. -/
noncomputable def heckePrimeEulerPolynomial
    (p : RationalPrime) (T : EisensteinQA) : EisensteinQA := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  if h2 : p.1 = 2 then
    exact 1
  else if h3 : p.1 = 3 then
    exact 1
  else
    exact heckeRationalPrimeEulerPolynomial p.1
      (goodPrime_gt_three p h2 h3) T

/-- Exact local equality for every proof-carrying rational prime, including the
conductor primes. -/
theorem elliptic_hecke_primePolynomial_agreement
    (p : RationalPrime) (T : EisensteinQA) :
    ellipticPrimeEulerPolynomial p T = heckePrimeEulerPolynomial p T := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  unfold ellipticPrimeEulerPolynomial heckePrimeEulerPolynomial
  by_cases h2 : p.1 = 2
  · simp [h2]
  · by_cases h3 : p.1 = 3
    · simp [h2, h3]
    · simp only [h2, h3, ↓reduceIte]
      exact hecke_elliptic_goodPrime_local_agreement p.1
        (goodPrime_gt_three p h2 h3) T |>.symm

/-- Finite elliptic Euler denominator over a selected prime set. -/
noncomputable def ellipticFiniteEulerDenominator
    (S : Finset RationalPrime) (T : EisensteinQA) : EisensteinQA :=
  ∏ p ∈ S, ellipticPrimeEulerPolynomial p T

/-- Finite Hecke Euler denominator over the same selected rational primes. -/
noncomputable def heckeFiniteEulerDenominator
    (S : Finset RationalPrime) (T : EisensteinQA) : EisensteinQA :=
  ∏ p ∈ S, heckePrimeEulerPolynomial p T

/-- Every finite Euler truncation agrees exactly. -/
theorem finiteEulerDenominator_agreement
    (S : Finset RationalPrime) (T : EisensteinQA) :
    ellipticFiniteEulerDenominator S T = heckeFiniteEulerDenominator S T := by
  unfold ellipticFiniteEulerDenominator heckeFiniteEulerDenominator
  apply Finset.prod_congr rfl
  intro p hp
  exact elliptic_hecke_primePolynomial_agreement p T

/-- The same theorem after embedding both finite products into any commutative
ring target. -/
theorem finiteEulerDenominator_agreement_map
    {R : Type*} [CommRing R]
    (f : EisensteinQA →+* R)
    (S : Finset RationalPrime) (T : EisensteinQA) :
    f (ellipticFiniteEulerDenominator S T) =
      f (heckeFiniteEulerDenominator S T) := by
  rw [finiteEulerDenominator_agreement]

structure FiniteEulerProductBoundary where
  everyPrimeLocalAgreementPaid : Bool := true
  everyFinitePrimeSetProductAgreementPaid : Bool := true
  conductorPrimesExcludedOnHeckeSidePaid : Bool := true
  finiteGlobalCompositionPaid : Bool := true
  infiniteEulerProductConvergencePaid : Bool := false
  analyticEulerProductEqualityPaid : Bool := false
  analyticHeckeLSeriesPaid : Bool := false
  ellipticHeckeLSeriesAgreementPaid : Bool := false

/-- Algebraic globalization is complete at every finite truncation. -/
def canonicalBoundary : FiniteEulerProductBoundary := {}

end Integration.EisensteinJZeroFiniteEulerProductExact
