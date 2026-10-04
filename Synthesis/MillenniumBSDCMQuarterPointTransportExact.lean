import Synthesis.MillenniumBSDCMGeometricKummerSquareClassEvaluationExact
import Synthesis.MillenniumBSDCMGlobalKummerOrdinaryExact
import Mathlib.Tactic

/-!
# BSD max-cut: reusable transport for explicit quarter-points

The remaining global boundary cases are finite arithmetic calculations on
explicit geometric halves.  This owner removes all repeated H¹ plumbing from
those calculations.

Given a literal custom Qbar point `Q` with `2Q=P`, we turn it into the exact
`GeometricHalfData` consumed by the genuine Kummer construction.  A pointwise
formula for `σQ-Q` on the custom carrier then becomes the corresponding
`(Z/2)^2` character value.  Finally half-choice independence transfers the
result to the repository's canonical chosen half.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve
open BSDCohomology

noncomputable section

/-- Any explicit custom Qbar half of a literal rational point can be inserted
directly into the genuine geometric Kummer construction. -/
noncomputable def cmCustomRationalGeometricHalfData
    (P : RationalProjectivePoint)
    (Q : CMAlgClosureProjectivePoint)
    (hdouble : (2 : ℕ) • Q = cmRationalPointToAlgClosure P) :
    GeometricHalfData cmWeierstrass (cmRationalGeometricPoint P) where
  half := cmAlgClosurePointAddEquivMathlib Q
  double_half := by
    change (2 : ℕ) • cmAlgClosurePointAddEquivMathlib Q =
      cmAlgClosurePointEquivMathlib (cmRationalPointToAlgClosure P)
    rw [← map_nsmul, hdouble]
    rfl

/-- The generic same-object transport: once the custom difference is a named
actual E[2] element, the transported trivial character has exactly the same
`(Z/2)^2` value. -/
theorem cmCustomRationalGeometricHalf_trivialCharacter_apply_of_difference
    (P : RationalProjectivePoint)
    (Q : CMAlgClosureProjectivePoint)
    (hdouble : (2 : ℕ) • Q = cmRationalPointToAlgClosure P)
    (σ : RationalAbsoluteGalois)
    (bits : CMTwoTorsionCarrier)
    (hdiff :
      cmAlgClosureGaloisAction σ Q - Q =
        (cmAlgClosureTwoTorsionEquiv bits).1) :
    Multiplicative.toAdd
      (cmGeometricKummerTrivialCharacter
        (cmRationalGeometricPoint_isGaloisFixed P)
        (cmCustomRationalGeometricHalfData P Q hdouble) σ) = bits := by
  apply cmAlgClosureTwoTorsionEquiv.injective
  apply Subtype.ext
  change cmAlgClosurePointAddEquivMathlib.symm
      (galoisPointMap cmWeierstrass σ
          (cmAlgClosurePointAddEquivMathlib Q) -
        cmAlgClosurePointAddEquivMathlib Q) =
    (cmAlgClosureTwoTorsionEquiv bits).1
  rw [map_sub]
  have hcomm := cmAlgClosurePointEquiv_galois_commutes σ Q
  change cmAlgClosurePointAddEquivMathlib
      (cmAlgClosureGaloisAction σ Q) =
    galoisPointMap cmWeierstrass σ
      (cmAlgClosurePointAddEquivMathlib Q) at hcomm
  rw [← hcomm]
  simp only [AddEquiv.symm_apply_apply]
  exact hdiff

/-- Once an explicit half has a known pair of scalar quadratic characters,
the canonical geometric Kummer square-class output is forced to be the inverse
paid scalar-Kummer image of that pair. -/
theorem cmRationalCohomologicalKummerSquareClass_eq_of_custom_characterPair
    (P : RationalProjectivePoint)
    (Q : CMAlgClosureProjectivePoint)
    (hdouble : (2 : ℕ) • Q = cmRationalPointToAlgClosure P)
    (chars : RationalQuadraticCharacter × RationalQuadraticCharacter)
    (hchar :
      cmTwoTorsionContinuousCharacterMulEquivPair
        (cmGeometricKummerTrivialCharacter
          (cmRationalGeometricPoint_isGaloisFixed P)
          (cmCustomRationalGeometricHalfData P Q hdouble)) = chars) :
    cmRationalCohomologicalKummerSquareClass P =
      quadraticCharacterPairMulEquivRatSquareClasses chars := by
  let GP : GeometricPoint cmWeierstrass := cmRationalGeometricPoint P
  let hP : IsGaloisFixedPoint cmWeierstrass GP :=
    cmRationalGeometricPoint_isGaloisFixed P
  let Qchosen : GeometricHalfData cmWeierstrass GP :=
    cmRationalGeometricHalfData P
  let Qexplicit : GeometricHalfData cmWeierstrass GP :=
    cmCustomRationalGeometricHalfData P Q hdouble
  have hind :
      cmGeometricKummerTrivialCharacter hP Qchosen =
        cmGeometricKummerTrivialCharacter hP Qexplicit :=
    cmGeometricKummerTrivialCharacter_half_independent hP Qchosen Qexplicit
  change cmGenericKummerE2H1MulEquivRatSquareClasses
      (Multiplicative.ofAdd
        (cmGeometricKummerGenericE2H1 hP Qchosen)) = _
  rw [cmGeometricKummerGenericE2H1_squareClass_evaluation]
  rw [hind]
  change quadraticCharacterPairMulEquivRatSquareClasses
      (cmTwoTorsionContinuousCharacterMulEquivPair
        (cmGeometricKummerTrivialCharacter hP Qexplicit)) = _
  rw [hchar]

/-!
MAX-CUT STATUS

All H¹/coefficient/half-choice plumbing for the three nonzero quarter-point
boundaries is now factored out.  Each boundary owner only has to prove:

1. an explicit `Q` satisfies `2Q=P`;
2. the literal custom difference `σQ-Q` is the expected actual E[2] point;
3. equivalently, the two transported scalar characters are the desired
   quadratic Kummer characters.

No additional cohomological architecture belongs in the boundary proofs.
-/

end

end Synthesis.Millennium.BSD
