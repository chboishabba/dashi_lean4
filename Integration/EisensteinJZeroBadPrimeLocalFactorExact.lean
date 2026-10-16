import Integration.EisensteinJZeroBadPrimeTwoExact
import Integration.EisensteinJZeroBadPrimeThreeExact

/-!
# Bad-prime local factors from the nonsingular reduction locus

Pinned Mathlib does not currently expose a Tate-algorithm/Kodaira API for this
curve.  That is not needed to compute the local Euler coefficients themselves.
For a singular Weierstrass reduction the standard bad-reduction coefficient is

    a_p = p - #E_ns(F_p),

where `E_ns(F_p)` is the nonsingular locus of the reduced cubic.  This file
formalizes that finite locus directly for the already-owned reductions at 2
and 3.

The calculation is entirely repo-owned finite arithmetic:

* over F_2 the reduced projective cubic has 3 points, exactly one affine
  singular point, and a nonsingular point at infinity, hence #E_ns=2;
* over F_3 it has 4 points, exactly one affine singular point, and a
  nonsingular point at infinity, hence #E_ns=3.

Therefore a_2=a_3=0 and both bad local factors are `1`.

Attribution boundary: the *definition/convention* of the bad local coefficient
via the nonsingular locus is standard elliptic-curve terminology; the literal
finite counts and derivative checks below are DASHI/Lean proofs over Mathlib's
`ZMod` infrastructure.  No external Kodaira symbol, conductor exponent, or
database row is promoted into a proof term.
-/

namespace Integration.EisensteinJZeroBadPrimeLocalFactorExact

open Integration.EisensteinJZeroBadPrimeTwoExact
open Integration.EisensteinJZeroBadPrimeThreeExact

------------------------------------------------------------------------
-- p = 2
------------------------------------------------------------------------

/-- Literal affine singularity predicate for the reduced cubic at two. -/
def badPrimeTwoAffineSingular (xy : ZMod 2 × ZMod 2) : Bool :=
  decide
    (reducedCurveTwoEquation xy.1 xy.2 ∧
      reducedCurveTwoDx xy.1 = 0 ∧ reducedCurveTwoDy xy.2 = 0)

/-- Number of affine singular points. -/
def badPrimeTwoAffineSingularCount : Nat :=
  ((Finset.univ : Finset (ZMod 2 × ZMod 2)).filter badPrimeTwoAffineSingular).card

/-- The explicit point `(0,1)` is the unique affine singularity. -/
theorem badPrimeTwoAffineSingularCount_exact :
    badPrimeTwoAffineSingularCount = 1 := by
  native_decide

/-- For `F(X,Y,Z)=Y²Z-X³-Z³`, the Z-partial at the Weierstrass point at
infinity `[0:1:0]` is one, so infinity is nonsingular even in characteristic
two. -/
def badPrimeTwoInfinityZDerivative : ZMod 2 :=
  (1 : ZMod 2) ^ 2 - 3 * (0 : ZMod 2) ^ 2

theorem badPrimeTwoInfinity_nonsingular :
    badPrimeTwoInfinityZDerivative ≠ 0 := by
  native_decide

/-- Nonsingular projective-locus count.  The naive projective owner already
proved that the reduced cubic has three rational projective points; exactly one
is singular and infinity is not it. -/
def badPrimeTwoNonsingularProjectiveCount : Nat :=
  reducedCurveTwoProjectiveNaivePointCount - badPrimeTwoAffineSingularCount

theorem badPrimeTwoNonsingularProjectiveCount_exact :
    badPrimeTwoNonsingularProjectiveCount = 2 := by
  rw [badPrimeTwoNonsingularProjectiveCount,
    reducedCurveTwoProjectiveNaivePointCount_exact,
    badPrimeTwoAffineSingularCount_exact]

/-- Standard bad-reduction coefficient `a_2 = 2 - #E_ns(F_2)`. -/
def badPrimeTwoLocalTrace : Int :=
  (2 : Int) - badPrimeTwoNonsingularProjectiveCount

theorem badPrimeTwoLocalTrace_zero : badPrimeTwoLocalTrace = 0 := by
  rw [badPrimeTwoLocalTrace, badPrimeTwoNonsingularProjectiveCount_exact]
  norm_num

------------------------------------------------------------------------
-- p = 3
------------------------------------------------------------------------

/-- Literal affine singularity predicate for the reduced cubic at three. -/
def badPrimeThreeAffineSingular (xy : ZMod 3 × ZMod 3) : Bool :=
  decide
    (reducedCurveThreeEquation xy.1 xy.2 ∧
      reducedCurveThreeDx xy.1 = 0 ∧ reducedCurveThreeDy xy.2 = 0)

/-- Number of affine singular points. -/
def badPrimeThreeAffineSingularCount : Nat :=
  ((Finset.univ : Finset (ZMod 3 × ZMod 3)).filter badPrimeThreeAffineSingular).card

/-- The explicit point `(2,0)` is the unique affine singularity. -/
theorem badPrimeThreeAffineSingularCount_exact :
    badPrimeThreeAffineSingularCount = 1 := by
  native_decide

/-- The point at infinity is nonsingular in characteristic three as well. -/
def badPrimeThreeInfinityZDerivative : ZMod 3 :=
  (1 : ZMod 3) ^ 2 - 3 * (0 : ZMod 3) ^ 2

theorem badPrimeThreeInfinity_nonsingular :
    badPrimeThreeInfinityZDerivative ≠ 0 := by
  native_decide

/-- Nonsingular projective-locus count. -/
def badPrimeThreeNonsingularProjectiveCount : Nat :=
  reducedCurveThreeProjectiveNaivePointCount - badPrimeThreeAffineSingularCount

theorem badPrimeThreeNonsingularProjectiveCount_exact :
    badPrimeThreeNonsingularProjectiveCount = 3 := by
  rw [badPrimeThreeNonsingularProjectiveCount,
    reducedCurveThreeProjectiveNaivePointCount_exact,
    badPrimeThreeAffineSingularCount_exact]

/-- Standard bad-reduction coefficient `a_3 = 3 - #E_ns(F_3)`. -/
def badPrimeThreeLocalTrace : Int :=
  (3 : Int) - badPrimeThreeNonsingularProjectiveCount

theorem badPrimeThreeLocalTrace_zero : badPrimeThreeLocalTrace = 0 := by
  rw [badPrimeThreeLocalTrace, badPrimeThreeNonsingularProjectiveCount_exact]
  norm_num

------------------------------------------------------------------------
-- Local Euler factors.
------------------------------------------------------------------------

/-- Linear bad-reduction local Euler polynomial `1-a_p T`. -/
def badLocalEulerFactor {R : Type*} [CommRing R] (a : Int) (T : R) : R :=
  1 - (a : R) * T

noncomputable def badPrimeTwoLocalEulerFactor {R : Type*} [CommRing R] (T : R) : R :=
  badLocalEulerFactor badPrimeTwoLocalTrace T

noncomputable def badPrimeThreeLocalEulerFactor {R : Type*} [CommRing R] (T : R) : R :=
  badLocalEulerFactor badPrimeThreeLocalTrace T

/-- Additive local factor at two is one. -/
theorem badPrimeTwoLocalEulerFactor_one
    {R : Type*} [CommRing R] (T : R) :
    badPrimeTwoLocalEulerFactor T = 1 := by
  rw [badPrimeTwoLocalEulerFactor, badPrimeTwoLocalTrace_zero]
  simp [badLocalEulerFactor]

/-- Additive local factor at three is one. -/
theorem badPrimeThreeLocalEulerFactor_one
    {R : Type*} [CommRing R] (T : R) :
    badPrimeThreeLocalEulerFactor T = 1 := by
  rw [badPrimeThreeLocalEulerFactor, badPrimeThreeLocalTrace_zero]
  simp [badLocalEulerFactor]

structure BadPrimeLocalFactorBoundary where
  p2UniqueAffineSingularityPaid : Bool := true
  p3UniqueAffineSingularityPaid : Bool := true
  infinityNonsingularAtTwoPaid : Bool := true
  infinityNonsingularAtThreePaid : Bool := true
  p2NonsingularLocusCountPaid : Bool := true
  p3NonsingularLocusCountPaid : Bool := true
  p2LocalTraceZeroPaid : Bool := true
  p3LocalTraceZeroPaid : Bool := true
  p2LocalFactorOnePaid : Bool := true
  p3LocalFactorOnePaid : Bool := true
  kodairaSymbolPaid : Bool := false
  conductorExponentPaid : Bool := false

/-- Bad local Euler factors are now paid independently of the still-external
Kodaira/conductor metadata. -/
def canonicalBoundary : BadPrimeLocalFactorBoundary := {}

end Integration.EisensteinJZeroBadPrimeLocalFactorExact
