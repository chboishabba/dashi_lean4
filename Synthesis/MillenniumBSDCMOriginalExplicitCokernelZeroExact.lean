import Synthesis.MillenniumBSDCMOriginalExplicitSelmerFourTorsionExact
import Synthesis.MillenniumBSDExplicitSelmerCokernelExact
import Synthesis.MillenniumBSDGlobalKummerTorsionTriangle
import Mathlib.Tactic

/-!
# BSD: exact global Kummer quotient and explicit cokernel on original objects

The existing global quotient-to-explicit-Selmer morphism has already
been proved injective. The selected-curve four-torsion description
provides a literal point lifting each of the four explicit Selmer
classes. Thus the original global Kummer map is surjective onto the
original explicit all-place Selmer subgroup.

This closes the ORIGINAL EXPLICIT Kummer cokernel and provides a
multiplicative equivalence E(Q)/2E(Q) ≃ explicitTwoSelmerSubgroup.
It does NOT identify the explicit Selmer subgroup with the continuous
cohomological Selmer, nor the explicit quotient with classical Sha[2].

All declarations are source-written; exact-head Lean kernel pending.
-/

namespace Synthesis.Millennium.BSD

/-- Literal rational torsion points corresponding to the original
four rational two-torsion enum constructors. -/
def cmRationalTorsionPointOfCode :
    RationalTwoTorsionPoint → RationalProjectivePoint
  | .infinity => 0
  | .zero => rationalZeroTorsionPoint
  | .one => rationalOneTorsionPoint
  | .negOne => rationalMinusOneTorsionPoint

/-- The original global Kummer map has precisely the original
torsionKummer code at each of those actual rational points. -/
theorem cmTotalGlobalKummer_torsionPointOfCode
    (T : RationalTwoTorsionPoint) :
    totalGlobalKummer (cmRationalTorsionPointOfCode T) =
      torsionKummer T := by
  cases T with
  | infinity =>
      simpa [cmRationalTorsionPointOfCode, torsionKummer]
        using totalGlobalKummer_zero
  | zero =>
      exact totalGlobalKummer_rationalZeroTorsion
  | one =>
      exact totalGlobalKummer_rationalOneTorsion
  | negOne =>
      exact totalGlobalKummer_rationalMinusOneTorsion

/-- Every one of the four original finite torsion Kummer elements is
in the range of the genuine group homomorphism from E(Q)/2E(Q). -/
theorem cmTorsionSelmerClass_in_globalKummerRange
    (T : RationalTwoTorsionPoint) :
    ∃ q : Multiplicative RationalProjectivePoint ⧸ globalDoubleSubgroup,
      globalKummerQuotientToSelmer q =
        cmTorsionCodeToOriginalExplicitSelmer T := by
  refine ⟨QuotientGroup.mk' globalDoubleSubgroup
    (Multiplicative.ofAdd (cmRationalTorsionPointOfCode T)), ?_⟩
  rw [globalKummerQuotientToSelmer_mk]
  apply Subtype.ext
  change totalGlobalKummer (cmRationalTorsionPointOfCode T) =
    torsionKummer T
  exact cmTotalGlobalKummer_torsionPointOfCode T

/-- Actual original global Kummer quotient surjects onto the literal
explicit Selmer subgroup on y²=x³-x. No synthetic dimension input. -/
theorem cmGlobalKummerQuotientToSelmer_surjective :
    Function.Surjective globalKummerQuotientToSelmer := by
  intro s
  obtain ⟨T, hT⟩ :=
    cmTorsionCodeToOriginalExplicitSelmer_surjective s
  obtain ⟨q, hq⟩ := cmTorsionSelmerClass_in_globalKummerRange T
  exact ⟨q, hq.trans hT⟩

/-- Exact original explicit arithmetic descent:
the actual rational point group modulo doubles is equivalent as
a group to the original all-place explicit two-Selmer subgroup. -/
noncomputable def cmGlobalKummerQuotientEquivExplicitSelmer :
    (Multiplicative RationalProjectivePoint ⧸ globalDoubleSubgroup) ≃*
      explicitTwoSelmerSubgroup :=
  MulEquiv.ofBijective globalKummerQuotientToSelmer
    ⟨globalKummerQuotientToSelmer_injective,
      cmGlobalKummerQuotientToSelmer_surjective⟩

/-- The original EXPLICIT Kummer cokernel is the trivial group.
This does not claim vanishing of classical Tate–Shafarevich. -/
theorem cmExplicitTwoSelmerCokernel_eq_one
    (x : ExplicitTwoSelmerCokernel) : x = 1 := by
  obtain ⟨s, rfl⟩ := explicitTwoSelmerCokernelMap_surjective x
  obtain ⟨q, hq⟩ := cmGlobalKummerQuotientToSelmer_surjective s
  rw [← hq]
  exact explicitTwoSelmerCokernelMap_after_globalKummer q

/-- An actual singleton statement about the original explicit
cokernel, not the cohomological Sha(E)[2] group. -/
theorem cmExplicitTwoSelmerCokernel_subsingleton :
    Subsingleton ExplicitTwoSelmerCokernel := by
  constructor
  intro x y
  exact (cmExplicitTwoSelmerCokernel_eq_one x).trans
    (cmExplicitTwoSelmerCokernel_eq_one y).symm

end Synthesis.Millennium.BSD
