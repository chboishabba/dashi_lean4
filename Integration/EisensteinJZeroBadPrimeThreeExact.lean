import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card

/-!
# Literal bad-prime-three reduction boundary for y^2 = x^3 + 1

The good-prime Euler polynomial machinery must not be reused at `p=3` merely
because an affine point count can still be executed.  The reduced cubic is
singular in characteristic three.

This owner pays exactly what is available without importing absent
Neron/Kodaira/reduction-type infrastructure:

* the reduced equation over `F_3`;
* an explicit singular point `(2,0)`;
* vanishing formal x/y derivatives there;
* the exact affine point count;
* the naive projective count after adjoining the unique Weierstrass point at
  infinity.

It deliberately does NOT call that naive projective count the good-reduction
elliptic point count and does not manufacture the bad-prime local L-factor.
The latter needs a reduction-type/conductor owner that pinned Mathlib does not
currently provide.

Attribution: this file is elementary repo-owned specialization. `ZMod` and
finite-set infrastructure are Mathlib-owned. No external scientific source is
introduced.
-/

namespace Integration.EisensteinJZeroBadPrimeThreeExact

/-- Reduced affine equation `y^2=x^3+1` over `F_3`. -/
def reducedCurveThreeEquation (x y : ZMod 3) : Prop :=
  y ^ 2 = x ^ 3 + 1

/-- Formal x-partial of `x^3+1-y^2` after reduction modulo three. -/
def reducedCurveThreeDx (x : ZMod 3) : ZMod 3 :=
  3 * x ^ 2

/-- Formal y-partial of `x^3+1-y^2`. -/
def reducedCurveThreeDy (y : ZMod 3) : ZMod 3 :=
  -2 * y

/-- `(2,0)` lies on the reduced cubic. -/
theorem badReductionSingularPoint_on_curve :
    reducedCurveThreeEquation (2 : ZMod 3) 0 := by
  native_decide

/-- The x-partial vanishes at the explicit point; indeed the cubic derivative
vanishes identically in characteristic three. -/
theorem badReductionSingularPoint_dx :
    reducedCurveThreeDx (2 : ZMod 3) = 0 := by
  native_decide

/-- The y-partial vanishes at the explicit point. -/
theorem badReductionSingularPoint_dy :
    reducedCurveThreeDy (0 : ZMod 3) = 0 := by
  native_decide

/-- Executable affine point count of the singular reduced cubic. -/
def reducedCurveThreeAffinePointCount : Nat :=
  ((Finset.univ : Finset (ZMod 3 × ZMod 3)).filter fun xy =>
    decide (reducedCurveThreeEquation xy.1 xy.2)).card

/-- The singular affine cubic has exactly three `F_3` points. -/
theorem reducedCurveThreeAffinePointCount_exact :
    reducedCurveThreeAffinePointCount = 3 := by
  native_decide

/-- Naive projective count obtained by adjoining the unique Weierstrass point
at infinity.  This is intentionally named `Naive`: bad reduction prevents the
good-prime Frobenius/Euler interpretation from being inferred automatically. -/
def reducedCurveThreeProjectiveNaivePointCount : Nat :=
  reducedCurveThreeAffinePointCount + 1

/-- The naive projective reduction has four points. -/
theorem reducedCurveThreeProjectiveNaivePointCount_exact :
    reducedCurveThreeProjectiveNaivePointCount = 4 := by
  native_decide

structure BadPrimeThreeBoundary where
  literalReducedEquationPaid : Bool := true
  explicitSingularPointPaid : Bool := true
  formalDerivativeVanishingPaid : Bool := true
  affinePointCountPaid : Bool := true
  naiveProjectiveCountPaid : Bool := true
  goodReductionInterpretationApplied : Bool := false
  neronKodairaReductionTypePaid : Bool := false
  conductorExponentPaid : Bool := false
  badPrimeEllipticLocalFactorPaid : Bool := false

/-- Exact boundary at the bad prime. -/
def canonicalBoundary : BadPrimeThreeBoundary := {}

end Integration.EisensteinJZeroBadPrimeThreeExact
