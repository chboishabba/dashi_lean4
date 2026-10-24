import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card

/-!
# Literal bad-prime-two reduction boundary for y^2 = x^3 + 1

The model also has bad reduction at `p=2`.  As at `p=3`, this owner pays only
the literal reduced cubic facts that do not require absent Neron/Kodaira
infrastructure:

* the reduced equation over `F_2`;
* an explicit singular point `(0,1)`;
* vanishing formal x/y derivatives there;
* exact affine and naive-projective finite counts.

These facts must not be fed through the good-reduction Euler-polynomial formula
without a separate reduction-type/conductor theorem.

Attribution: `ZMod` and finite-set infrastructure are Mathlib-owned.  The
specialized finite computation is DASHI/Lean-owned.  No external scientific
source authority is created by this file.
-/

namespace Integration.EisensteinJZeroBadPrimeTwoExact

/-- Reduced affine equation `y^2=x^3+1` over `F_2`. -/
def reducedCurveTwoEquation (x y : ZMod 2) : Prop :=
  y ^ 2 = x ^ 3 + 1

/-- Formal x-partial of `x^3+1-y^2` reduced modulo two. -/
def reducedCurveTwoDx (x : ZMod 2) : ZMod 2 :=
  3 * x ^ 2

/-- Formal y-partial. -/
def reducedCurveTwoDy (y : ZMod 2) : ZMod 2 :=
  -2 * y

/-- `(0,1)` lies on the reduced cubic. -/
theorem badReductionSingularPoint_on_curve :
    reducedCurveTwoEquation (0 : ZMod 2) 1 := by
  native_decide

/-- The x-partial vanishes at the explicit point. -/
theorem badReductionSingularPoint_dx :
    reducedCurveTwoDx (0 : ZMod 2) = 0 := by
  native_decide

/-- The y-partial vanishes identically in characteristic two and in particular
at the explicit point. -/
theorem badReductionSingularPoint_dy :
    reducedCurveTwoDy (1 : ZMod 2) = 0 := by
  native_decide

/-- Executable affine point count of the singular reduced cubic. -/
def reducedCurveTwoAffinePointCount : Nat :=
  ((Finset.univ : Finset (ZMod 2 × ZMod 2)).filter fun xy =>
    decide (reducedCurveTwoEquation xy.1 xy.2)).card

/-- The singular affine cubic has exactly two `F_2` points. -/
theorem reducedCurveTwoAffinePointCount_exact :
    reducedCurveTwoAffinePointCount = 2 := by
  native_decide

/-- Naive projective count after adjoining the usual point at infinity. -/
def reducedCurveTwoProjectiveNaivePointCount : Nat :=
  reducedCurveTwoAffinePointCount + 1

/-- The naive projective reduction has three points. -/
theorem reducedCurveTwoProjectiveNaivePointCount_exact :
    reducedCurveTwoProjectiveNaivePointCount = 3 := by
  native_decide

structure BadPrimeTwoBoundary where
  literalReducedEquationPaid : Bool := true
  explicitSingularPointPaid : Bool := true
  formalDerivativeVanishingPaid : Bool := true
  affinePointCountPaid : Bool := true
  naiveProjectiveCountPaid : Bool := true
  goodReductionInterpretationApplied : Bool := false
  neronKodairaReductionTypePaid : Bool := false
  conductorExponentPaid : Bool := false
  badPrimeEllipticLocalFactorPaid : Bool := false

/-- Exact boundary at the bad prime two. -/
def canonicalBoundary : BadPrimeTwoBoundary := {}

end Integration.EisensteinJZeroBadPrimeTwoExact
