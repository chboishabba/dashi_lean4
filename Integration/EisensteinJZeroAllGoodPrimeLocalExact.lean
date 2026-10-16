import Integration.EisensteinJZeroInertPrimeLocalFactorExact
import Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact
import Integration.EisensteinJZeroSplitPrimeUnitNormalizationExact

/-!
# Complete good-prime local classification for the j=0 Eisenstein curve

For every rational prime `p > 3`, the residue class modulo three is either
split (`1`) or inert (`2`).  The branch now owns both same-prime cases on the
same concrete curve `E : y^2 = x^3 + 1`:

* `p % 3 = 2`: `a_p = 0`, local polynomial `1 + p*T^2`;
* `p % 3 = 1`: the canonical Jacobi sum pulls back to a literal
  `z = a+b*omega : EisensteinQA` with `N(z)=p` and
  `a_p = -(2*a-b)`, hence local polynomial
  `1 + (2*a-b)*T + p*T^2`.

This closes the finite/local prime-by-prime classification away from the bad
prime `3`.  It does NOT construct a Groessencharacter or prove a global Euler
product/L-function theorem; those remain separate global payments.

Attribution: the inert and split local theorems are existing DASHI/Lean #69
owners; Mathlib infrastructure used by those owners remains attributed to
Mathlib.  This file owns only the same-prime case split/composition.
-/

namespace Integration.EisensteinJZeroAllGoodPrimeLocalExact

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroFiniteFieldTraceExact
open Integration.EisensteinJZeroInertPrimeLocalFactorExact
open Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact
open Integration.EisensteinJZeroSplitPrimeUnitNormalizationExact

/-- Exact local classification at a good rational prime. -/
inductive GoodPrimeLocalData (p : Nat) [Fact p.Prime] : Type where
  | split
      (hpmod : p % 3 = 1)
      (eisensteinFactor : EisensteinQA)
      (factorNorm : QuadraticAlgebra.norm eisensteinFactor = p)
      (frobeniusTrace :
        jZeroFrobeniusTraceInt (ZMod p) =
          -(2 * eisensteinFactor.re - eisensteinFactor.im))
      (normalizedCode : Dashi.EisensteinSixUnitOrbitExact.NormFiberCode p)
      (normalizedDecode :
        (Dashi.EisensteinSixUnitOrbitExact.decodeNormFiberCode p
          Fact.out.pos
          (splitPrimeInertEven p hpmod)
          normalizedCode).1 = eisensteinFactor)
  | inert
      (hpmod : p % 3 = 2)
      (frobeniusTrace : jZeroFrobeniusTraceInt (ZMod p) = 0)

private theorem goodPrime_mod_three_cases
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p) :
    p % 3 = 1 ∨ p % 3 = 2 := by
  have hpne3 : p ≠ 3 := by omega
  have hnot0 : p % 3 ≠ 0 := by
    intro h0
    have h3dvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    rcases (Nat.dvd_prime Fact.out).1 h3dvd with h31 | h3p
    · norm_num at h31
    · exact hpne3 h3p.symm
  have hlt : p % 3 < 3 := Nat.mod_lt p (by norm_num)
  omega

/-- Assemble the complete local datum from the exact split/inert source owners. -/
noncomputable def goodPrimeLocalData
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p) :
    GoodPrimeLocalData p := by
  rcases goodPrime_mod_three_cases p hp3 with hsplit | hinert
  · let z := splitJacobiEisensteinElement p (by omega) hsplit
    let code := splitJacobiNormFiberCode p (by omega) hsplit
    exact .split hsplit z
      (splitJacobiEisensteinElement_norm p (by omega) hsplit)
      (splitPrime_jZero_trace_formula p (by omega) hsplit)
      code
      (by
        simpa [z, code] using
          decode_splitJacobiNormFiberCode p (by omega) hsplit)
  · exact .inert hinert
      (jZeroInertPrime_trace_zero p (by omega) hinert)

/-- The actual same-curve good-prime Euler polynomial, independent of how the
prime is classified. -/
def goodPrimeLocalEulerPolynomial
    (p : Nat) [Fact p.Prime] (_hp3 : 3 < p) : Int → Int :=
  fun T => 1 - jZeroFrobeniusTraceInt (ZMod p) * T + p * T ^ 2

/-- The unified local polynomial is definitionally the same curve's local
Euler polynomial. -/
theorem goodPrimeLocalEulerPolynomial_eq_curve
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p) :
    goodPrimeLocalEulerPolynomial p hp3 =
      fun T => 1 - jZeroFrobeniusTraceInt (ZMod p) * T + p * T ^ 2 :=
  rfl

/-- Split good primes have the literal Eisenstein-coordinate local factor. -/
theorem goodPrimeLocalEulerPolynomial_split
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p) (hmod : p % 3 = 1) :
    goodPrimeLocalEulerPolynomial p hp3 =
      fun T => 1 +
        (2 * (splitJacobiEisensteinElement p (by omega) hmod).re
          - (splitJacobiEisensteinElement p (by omega) hmod).im) * T
        + p * T ^ 2 := by
  funext T
  simp only [goodPrimeLocalEulerPolynomial,
    splitPrime_jZero_trace_formula p (by omega) hmod]
  ring

/-- Inert good primes have trace-zero local factor. -/
theorem goodPrimeLocalEulerPolynomial_inert
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p) (hmod : p % 3 = 2) :
    goodPrimeLocalEulerPolynomial p hp3 =
      fun T => 1 + p * T ^ 2 := by
  funext T
  simp only [goodPrimeLocalEulerPolynomial,
    jZeroInertPrime_trace_zero p (by omega) hmod]
  ring

/-- Machine-readable local completion boundary. -/
structure AllGoodPrimeLocalBoundary where
  everyPrimeAboveThreeClassifiedSplitOrInert : Bool := true
  inertLocalFactorPaid : Bool := true
  splitLiteralEisensteinFactorPaid : Bool := true
  splitNormEqualsPrimePaid : Bool := true
  splitTraceFormulaPaid : Bool := true
  splitSixUnitNormalizationPaid : Bool := true
  allGoodPrimeSameCurveLocalPolynomialPaid : Bool := true
  badPrimeThreeLocalFactorPaid : Bool := false
  groessencharacterPaid : Bool := false
  globalEulerProductAgreementPaid : Bool := false
  globalEllipticLFunctionPaid : Bool := false

/-- Local good-prime programme is complete; global packaging is not. -/
def canonicalBoundary : AllGoodPrimeLocalBoundary := {}

end Integration.EisensteinJZeroAllGoodPrimeLocalExact
