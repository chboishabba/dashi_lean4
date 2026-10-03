import Synthesis.MillenniumBSDCMGeometricKummerSquareClassEvaluationExact
import Synthesis.MillenniumBSDCMXTOrientationExact
import Mathlib.Tactic

/-!
# Selected CM curve: ordinary global geometric Kummer = x-T

This owner closes the non-two-torsion affine part of the global comparison.
Algebraic closedness supplies explicit roots a,b,c with the required product
sign.  The previous owners compute their geometric Kummer character and its
H¹ square-class image.  Character-level half independence then transfers the
result from that explicit half to the canonical chosen half used by
`cmRationalGeometricKummerH1`.
-/

namespace Synthesis.Millennium.BSD

open WeierstrassCurve
open BSDCohomology

noncomputable section

/-- Root data needed by the explicit half exists for every Qbar affine point. -/
theorem cmHalfRootData_exists
    {x y : RatAlgClosure}
    (hcurve : y ^ 2 = x ^ 3 - x) :
    ∃ a b c : RatAlgClosure,
      a ^ 2 = x ∧
      b ^ 2 = x - 1 ∧
      c ^ 2 = x + 1 ∧
      a * b * c = -y := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq x (by norm_num : 0 < 2)
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (x - 1) (by norm_num : 0 < 2)
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (x + 1) (by norm_num : 0 < 2)
  have hsq : (a * b * c) ^ 2 = y ^ 2 := by
    rw [mul_pow, mul_pow, ha, hb, hc, hcurve]
    ring
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with habcPos | habcNeg
  · refine ⟨-a, b, c, ?_, hb, hc, ?_⟩
    · simpa using ha
    · rw [habcPos]
      ring
  · exact ⟨a, b, c, ha, hb, hc, habcNeg⟩

/-- Half independence propagates from the generic E[2]-valued character to
its transported trivial `(Z/2)^2` character. -/
theorem cmGeometricKummerTrivialCharacter_half_independent
    {P : GeometricPoint cmWeierstrass}
    (hP : IsGaloisFixedPoint cmWeierstrass P)
    (Q₁ Q₂ : GeometricHalfData cmWeierstrass P) :
    cmGeometricKummerTrivialCharacter hP Q₁ =
      cmGeometricKummerTrivialCharacter hP Q₂ := by
  apply ContinuousMonoidHom.ext
  intro σ
  apply Multiplicative.toAdd_injective
  change cmActualE2ContRepresentationEquiv.symm
      (cmGenericKummerE2ToActualTopRep
        (Multiplicative.toAdd (cmGeometricKummerContinuousCharacter hP Q₁ σ))) =
    cmActualE2ContRepresentationEquiv.symm
      (cmGenericKummerE2ToActualTopRep
        (Multiplicative.toAdd (cmGeometricKummerContinuousCharacter hP Q₂ σ)))
  rw [cmGeometricKummerContinuousCharacter_half_independent hP Q₁ Q₂]

/-- For an ordinary rational affine point, the raw geometric square-class
coordinates are exactly the swap of the explicit x-T coordinates. -/
theorem cmRationalCohomologicalKummer_raw_eq_swap_ordinary
    {x y : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy0 : y ≠ 0)
    (hx0 : x ≠ 0)
    (hx1 : x ≠ 1) :
    cmRationalCohomologicalKummerSquareClass
        (.affine x y hcurve) =
      ratSquareClassPairSwap
        (squareClassOf ⟨x, hx0⟩,
          squareClassOf ⟨x - 1, sub_ne_zero.mpr hx1⟩) := by
  have hcurve' :
      (y : RatAlgClosure) ^ 2 =
        (x : RatAlgClosure) ^ 3 - (x : RatAlgClosure) := by
    exact_mod_cast hcurve
  obtain ⟨a, b, c, ha, hb, hc, habc⟩ := cmHalfRootData_exists hcurve'
  let P : GeometricPoint cmWeierstrass :=
    cmRationalGeometricPoint (.affine x y hcurve)
  let hP : IsGaloisFixedPoint cmWeierstrass P :=
    cmRationalGeometricPoint_isGaloisFixed (.affine x y hcurve)
  let Qchosen : GeometricHalfData cmWeierstrass P :=
    cmRationalGeometricHalfData (.affine x y hcurve)
  let Qexplicit : GeometricHalfData cmWeierstrass P :=
    cmExplicitRationalGeometricHalfData hcurve ha hb hc habc
  have hchar :
      cmGeometricKummerTrivialCharacter hP Qchosen =
        cmGeometricKummerTrivialCharacter hP Qexplicit :=
    cmGeometricKummerTrivialCharacter_half_independent hP Qchosen Qexplicit
  change cmGenericKummerE2H1MulEquivRatSquareClasses
      (Multiplicative.ofAdd
        (cmGeometricKummerGenericE2H1 hP Qchosen)) = _
  rw [cmGeometricKummerGenericE2H1_squareClass_evaluation]
  rw [hchar]
  rw [cmExplicitRationalGeometricHalf_characterPair
    hcurve hy0 hx0 hx1 ha hb hc habc]
  exact cmRawGeometricQuadraticCharacterPair_toSquareClasses x hx0 hx1

/-- Same theorem stated against the repository's literal `totalGlobalKummer`
on ordinary non-two-torsion affine points. -/
theorem cmRationalCohomologicalKummer_raw_eq_swap_totalGlobal_ordinary
    {x y : ℚ}
    (hcurve : y ^ 2 = x ^ 3 - x)
    (hy0 : y ≠ 0)
    (hx0 : x ≠ 0)
    (hx1 : x ≠ 1) :
    cmRationalCohomologicalKummerSquareClass (.affine x y hcurve) =
      ratSquareClassPairSwap (totalGlobalKummer (.affine x y hcurve)) := by
  rw [cmRationalCohomologicalKummer_raw_eq_swap_ordinary hcurve hy0 hx0 hx1]
  simp [totalGlobalKummer, hx0, hx1, ordinaryKummer]

/-!
MAX-CUT STATUS

PAID HERE, subject to exact-head kernel certification:
* explicit root data exists without extra hypotheses;
* trivial-character half independence is propagated through the same-object
  coefficient transport;
* every affine rational point with y ≠ 0 satisfies the exact raw geometric
  orientation theorem against `totalGlobalKummer`.

ONLY GLOBAL CASES LEFT:
* infinity;
* (0,0), (1,0), (-1,0).
These are four finite boundary computations, not a remaining ordinary Kummer
or cohomology theorem.
-/

end

end Synthesis.Millennium.BSD
