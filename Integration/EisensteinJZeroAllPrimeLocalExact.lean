import Integration.EisensteinJZeroAllGoodPrimeLocalExact
import Integration.EisensteinJZeroBadPrimeLocalFactorExact

/-!
# Complete rational-prime local Euler compiler for y^2=x^3+1

This owner composes the already-paid good-prime split/inert classification with
the independently-computed nonsingular-locus factors at the two bad primes.
It gives one prime-indexed local polynomial on the SAME concrete j=0 curve:

* p=2: 1;
* p=3: 1;
* p>3, p≡1 mod3: 1-a_p T+pT² with the literal Eisenstein/Jacobi factor;
* p>3, p≡2 mod3: 1+pT².

This is a finite/local compiler only.  It does not itself form an analytic
Euler product, a Hecke character, or identify global L-functions.
-/

namespace Integration.EisensteinJZeroAllPrimeLocalExact

open Integration.EisensteinJZeroAllGoodPrimeLocalExact
open Integration.EisensteinJZeroBadPrimeLocalFactorExact

/-- Unified local Euler polynomial at a rational prime. -/
noncomputable def allPrimeLocalEulerPolynomial
    (p : Nat) [Fact p.Prime] : Int → Int :=
  if h2 : p = 2 then
    fun T => badPrimeTwoLocalEulerFactor T
  else if h3 : p = 3 then
    fun T => badPrimeThreeLocalEulerFactor T
  else
    goodPrimeLocalEulerPolynomial p (by
      have hp2 := Fact.out.two_le
      omega)

/-- The bad factor at two is exactly one. -/
theorem allPrimeLocalEulerPolynomial_two :
    allPrimeLocalEulerPolynomial 2 = fun _ : Int => 1 := by
  funext T
  simp [allPrimeLocalEulerPolynomial, badPrimeTwoLocalEulerFactor_one]

/-- The bad factor at three is exactly one. -/
theorem allPrimeLocalEulerPolynomial_three :
    allPrimeLocalEulerPolynomial 3 = fun _ : Int => 1 := by
  funext T
  simp [allPrimeLocalEulerPolynomial, badPrimeThreeLocalEulerFactor_one]

/-- Away from the two bad primes the compiler is definitionally the existing
good-prime same-curve local polynomial. -/
theorem allPrimeLocalEulerPolynomial_good
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p) :
    allPrimeLocalEulerPolynomial p = goodPrimeLocalEulerPolynomial p hp3 := by
  have h2 : p ≠ 2 := by omega
  have h3 : p ≠ 3 := by omega
  simp [allPrimeLocalEulerPolynomial, h2, h3]

/-- Split-prime specialization. -/
theorem allPrimeLocalEulerPolynomial_split
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p) (hmod : p % 3 = 1) :
    allPrimeLocalEulerPolynomial p =
      fun T => 1 +
        (2 * (Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact.splitJacobiEisensteinElement
          p (by omega) hmod).re
          - (Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact.splitJacobiEisensteinElement
            p (by omega) hmod).im) * T
        + p * T ^ 2 := by
  rw [allPrimeLocalEulerPolynomial_good p hp3]
  exact goodPrimeLocalEulerPolynomial_split p hp3 hmod

/-- Inert-prime specialization. -/
theorem allPrimeLocalEulerPolynomial_inert
    (p : Nat) [Fact p.Prime] (hp3 : 3 < p) (hmod : p % 3 = 2) :
    allPrimeLocalEulerPolynomial p = fun T => 1 + p * T ^ 2 := by
  rw [allPrimeLocalEulerPolynomial_good p hp3]
  exact goodPrimeLocalEulerPolynomial_inert p hp3 hmod

/-- Machine-readable complete local classification. -/
inductive RationalPrimeLocalKind
  | badTwo
  | badThree
  | splitGood
  | inertGood
  deriving DecidableEq, Repr

noncomputable def rationalPrimeLocalKind
    (p : Nat) [Fact p.Prime] : RationalPrimeLocalKind :=
  if p = 2 then .badTwo
  else if p = 3 then .badThree
  else if p % 3 = 1 then .splitGood
  else .inertGood

structure AllPrimeLocalBoundary where
  badTwoLocalFactorPaid : Bool := true
  badThreeLocalFactorPaid : Bool := true
  everyGoodPrimeClassifiedPaid : Bool := true
  everyRationalPrimeLocalPolynomialPaid : Bool := true
  analyticEulerProductPaid : Bool := false
  groessencharacterPaid : Bool := false
  sameCurveEulerProductAgreementPaid : Bool := false
  globalEllipticHeckeLSeriesPaid : Bool := false

/-- The local rational-prime layer is complete. -/
def canonicalBoundary : AllPrimeLocalBoundary := {}

end Integration.EisensteinJZeroAllPrimeLocalExact
