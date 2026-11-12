import Synthesis.MillenniumBSDCMOriginalMordellWeilModTwoCardExact
import Synthesis.MillenniumBSDRationalTwoTorsionExact
import Mathlib.Tactic

/-!
# BSD selected curve — every mod-doubling class has a rational 2-torsion lift

This is a genuine theorem on the original rational elliptic point group,
its original double subgroup, and its original quotient. The prior
all-prime explicit Selmer result is used only through the existing
Kummer quotient bijectivity. The rational two-torsion classification is
the already-written literal theorem in
MillenniumBSDRationalTwoTorsionExact.

No Mordell–Weil finite-generation or rank theorem is assumed or claimed
here. The local kernel needs to check this source before admission.
-/

namespace Synthesis.Millennium.BSD

/-- Every one of the four original rational codes is a literal point
annihilated by multiplication by two. -/
theorem cmRationalTorsionCode_double_zero
    (T : RationalTwoTorsionPoint) :
    (2 : ℕ) • cmRationalTorsionPointOfCode T = 0 := by
  cases T with
  | infinity => simp [cmRationalTorsionPointOfCode]
  | zero => exact rationalZeroTorsion_two_nsmul_zero
  | one => exact rationalOneTorsion_two_nsmul_zero
  | negOne => exact rationalMinusOneTorsion_two_nsmul_zero

/-- The ORIGINAL E(Q)/2E(Q) quotient is exhausted by images of actual
rational two-torsion points, not merely Boolean candidate codes. -/
theorem cmOriginalMWModTwo_everyClass_has_twoTorsionLift
    (q : Multiplicative RationalProjectivePoint ⧸ globalDoubleSubgroup) :
    ∃ T : RationalTwoTorsionPoint,
      q = QuotientGroup.mk' globalDoubleSubgroup
        (Multiplicative.ofAdd (cmRationalTorsionPointOfCode T)) := by
  obtain ⟨T, hT⟩ :=
    cmTorsionCodeToOriginalExplicitSelmer_surjective
      (globalKummerQuotientToSelmer q)
  have hLift := cmTorsionSelmerClass_in_globalKummerRange T
  let qT :=
    QuotientGroup.mk' globalDoubleSubgroup
      (Multiplicative.ofAdd (cmRationalTorsionPointOfCode T))
  have hLocal :
      globalKummerQuotientToSelmer qT =
        cmTorsionCodeToOriginalExplicitSelmer T := by
    dsimp [qT]
    rw [globalKummerQuotientToSelmer_mk]
    apply Subtype.ext
    change totalGlobalKummer (cmRationalTorsionPointOfCode T) =
      torsionKummer T
    exact cmTotalGlobalKummer_torsionPointOfCode T
  refine ⟨T, ?_⟩
  exact globalKummerQuotientToSelmer_injective
    (hT.symm.trans hLocal.symm)

/-- Every quotient representative can be selected from the actual
rational E(Q)[2] subgroup. The remaining K3 theorem is the
finite-generation/rank-vs-mod-two result, not enumeration. -/
theorem cmOriginalMWModTwo_has_actual_twoTorsion_representative
    (q : Multiplicative RationalProjectivePoint ⧸ globalDoubleSubgroup) :
    ∃ P : RationalProjectivePoint,
      (2 : ℕ) • P = 0 ∧
      QuotientGroup.mk' globalDoubleSubgroup
        (Multiplicative.ofAdd P) = q := by
  obtain ⟨T, hT⟩ := cmOriginalMWModTwo_everyClass_has_twoTorsionLift q
  exact ⟨cmRationalTorsionPointOfCode T,
    cmRationalTorsionCode_double_zero T, hT.symm⟩

end Synthesis.Millennium.BSD
