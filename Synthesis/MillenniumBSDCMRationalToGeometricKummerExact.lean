import Synthesis.MillenniumBSDActualRationalPointGroup
import Synthesis.MillenniumBSDActualE2GaloisFixed
import Synthesis.MillenniumBSDCMAlgClosureDoublingSurjectiveExact
import Synthesis.MillenniumBSDCMGeometricKummerContinuousH1Exact
import Mathlib.Tactic

/-!
# Selected CM curve: literal E(Q) points enter the geometric Kummer pipeline

The explicit x-T descent lane uses `RationalProjectivePoint`, while the genuine
continuous-cohomology lane uses the Mathlib point group over `AlgebraicClosure
ℚ`.  This file identifies those domains on the selected curve by the obvious
coordinate embedding and proves that every embedded rational point is fixed by
G_Q.

Surjectivity of geometric doubling then supplies a chosen half for every
literal rational point, so the continuous geometric Kummer H¹ constructor can
be applied directly to the same `RationalProjectivePoint` consumed by
`totalGlobalKummer`.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve
open BSDCohomology

noncomputable section

/-- Coordinatewise embedding of the repository's literal rational projective
point into the already-used Qbar projective carrier. -/
def cmRationalPointToAlgClosure :
    RationalProjectivePoint → CMAlgClosureProjectivePoint
  | .infinity => .infinity
  | .affine x y h =>
      .affine (x : RatAlgClosure) (y : RatAlgClosure) (by
        exact_mod_cast h)

@[simp] theorem cmRationalPointToAlgClosure_infinity :
    cmRationalPointToAlgClosure .infinity = .infinity := rfl

@[simp] theorem cmRationalPointToAlgClosure_affine
    (x y : ℚ) (h : y ^ 2 = x ^ 3 - x) :
    cmRationalPointToAlgClosure (.affine x y h) =
      .affine (x : RatAlgClosure) (y : RatAlgClosure) (by exact_mod_cast h) := rfl

/-- The custom coordinate action and the genuine Mathlib point action agree
under the already-existing point equivalence. -/
theorem cmAlgClosurePointEquiv_galoisAction
    (σ : RationalAbsoluteGalois)
    (P : CMAlgClosureProjectivePoint) :
    cmAlgClosurePointEquivMathlib (cmAlgClosureGaloisAction σ P) =
      galoisPointMap cmWeierstrass σ (cmAlgClosurePointEquivMathlib P) := by
  cases P with
  | infinity =>
      simp [cmAlgClosureGaloisAction, cmAlgClosurePointEquivMathlib,
        galoisPointMap]
  | affine x y h =>
      simp [cmAlgClosureGaloisAction, cmAlgClosurePointEquivMathlib,
        galoisPointMap]

/-- Rational coordinates are fixed by every Q-algebra automorphism. -/
theorem cmRationalPointToAlgClosure_galoisFixed
    (σ : RationalAbsoluteGalois)
    (P : RationalProjectivePoint) :
    cmAlgClosureGaloisAction σ (cmRationalPointToAlgClosure P) =
      cmRationalPointToAlgClosure P := by
  cases P with
  | infinity => simp [cmRationalPointToAlgClosure, cmAlgClosureGaloisAction]
  | affine x y h =>
      simp [cmRationalPointToAlgClosure, cmAlgClosureGaloisAction]

/-- Literal rational point as the exact geometric point carrier consumed by
`geometricPointTopRep cmWeierstrass`. -/
noncomputable def cmRationalGeometricPoint
    (P : RationalProjectivePoint) : GeometricPoint cmWeierstrass :=
  cmAlgClosurePointEquivMathlib (cmRationalPointToAlgClosure P)

/-- Every literal E(Q) point is fixed by the actual absolute-Galois point
transport. -/
theorem cmRationalGeometricPoint_isGaloisFixed
    (P : RationalProjectivePoint) :
    IsGaloisFixedPoint cmWeierstrass (cmRationalGeometricPoint P) := by
  intro σ
  rw [← cmAlgClosurePointEquiv_galoisAction]
  rw [cmRationalPointToAlgClosure_galoisFixed]

/-- A geometric half exists for every literal rational point by the already
proved surjectivity of multiplication by two on E(Qbar). -/
noncomputable def cmRationalGeometricHalfData
    (P : RationalProjectivePoint) :
    GeometricHalfData cmWeierstrass (cmRationalGeometricPoint P) := by
  obtain ⟨Q, hQ⟩ := cmGeometricDoubling_surjective (cmRationalGeometricPoint P)
  exact ⟨Q, hQ⟩

/-- Direct geometric Kummer H¹ class attached to the same literal rational
point used by `totalGlobalKummer`. -/
noncomputable def cmRationalGeometricKummerH1
    (P : RationalProjectivePoint) :
    continuousCohomology 1 CMGenericKummerE2TopRep :=
  cmGeometricKummerGenericE2H1
    (cmRationalGeometricPoint_isGaloisFixed P)
    (cmRationalGeometricHalfData P)

/-- Its square-class image is now a concrete function on the exact same domain
as the explicit x-T Kummer map.  The next theorem is equality of these two
functions, not a comparison between unrelated carriers. -/
noncomputable def cmRationalCohomologicalKummerSquareClass
    (P : RationalProjectivePoint) : RatSquareClass × RatSquareClass :=
  cmGenericKummerE2H1MulEquivRatSquareClasses
    (cmRationalGeometricKummerH1 P)

/-!
MAX-CUT STATUS

PAID HERE (subject to exact-head kernel certification):
* literal RationalProjectivePoint -> exact geometric Mathlib point carrier;
* compatibility of custom and generic Galois actions;
* every embedded rational point is G_Q-fixed;
* selected geometric [2]-surjectivity supplies a half for every rational point;
* the direct continuous Kummer H¹ class and its paid square-class image are now
  functions on the exact same rational-point domain as `totalGlobalKummer`.

DECISIVE NEXT SAME-OBJECT THEOREM:

  cmRationalCohomologicalKummerSquareClass P = totalGlobalKummer P.

That equality is the global x-T/cohomological Kummer weld.  After it, repeat
locally and prove localization naturality before identifying Selmer kernels.
-/

end

end Synthesis.Millennium.BSD
