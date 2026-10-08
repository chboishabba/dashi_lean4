import LeanDojoCoordinateLinearEquiv
import Gap
import Mathlib.Analysis.Calculus.FDeriv.Equiv

noncomputable section

open ClaySpec
open NavierStokes

namespace DASHILiteralClayNS

theorem pairCLE_preimage_global :
    pairLeanSpacetimeContinuousLinearEquiv ⁻¹'
        global_spacetime_domain 3 = nonnegativeTime := by
  ext z
  exact pairToLeanSpacetime_nonnegative_iff z

theorem pairCLE_symm_preimage_nonnegative :
    pairLeanSpacetimeContinuousLinearEquiv.symm ⁻¹' nonnegativeTime =
      global_spacetime_domain 3 := by
  ext z
  exact leanSpacetimeToPair_nonnegative_iff z

theorem uniqueDiffOn_leanDojoGlobal :
    UniqueDiffOn ℝ (global_spacetime_domain 3) := by
  apply pairLeanSpacetimeContinuousLinearEquiv.uniqueDiffOn_preimage_iff.mp
  simpa [pairCLE_preimage_global] using SemanticGap.uniqueDiffOn_nonnegativeTime

theorem iteratedFDerivWithin_comparatorFieldToLean
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : R3 → ℝ → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) nonnegativeTime)
    (n : ℕ) (z : Spacetime3) (hz : z ∈ global_spacetime_domain 3) :
    iteratedFDerivWithin ℝ n (comparatorFieldToLean f)
        (global_spacetime_domain 3) z =
      (iteratedFDerivWithin ℝ n (Function.uncurry f) nonnegativeTime
          (leanSpacetimeToPair z)).compContinuousLinearMap
        (fun _ => pairLeanSpacetimeContinuousLinearEquiv.symm.toContinuousLinearMap) := by
  rw [comparatorFieldToLean_eq_comp_symm]
  have hpre :
      pairLeanSpacetimeContinuousLinearEquiv.symm ⁻¹' nonnegativeTime =
        global_spacetime_domain 3 := pairCLE_symm_preimage_nonnegative
  have hx : pairLeanSpacetimeContinuousLinearEquiv.symm z ∈ nonnegativeTime := by
    simpa [pairLeanSpacetimeContinuousLinearEquiv_symm_apply] using
      (leanSpacetimeToPair_nonnegative_iff z).2 hz
  have h := ContinuousLinearMap.iteratedFDerivWithin_comp_right
    pairLeanSpacetimeContinuousLinearEquiv.symm.toContinuousLinearMap
    hf SemanticGap.uniqueDiffOn_nonnegativeTime
    (by simpa [hpre] using uniqueDiffOn_leanDojoGlobal)
    hx (i := n) (by simp)
  simpa [hpre, pairLeanSpacetimeContinuousLinearEquiv_symm_apply] using h

theorem iteratedFDerivWithin_leanField_eq_pullback
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Spacetime3 → E}
    (hf : ContDiffOn ℝ ∞ f (global_spacetime_domain 3))
    (n : ℕ) (z : Spacetime3) (hz : z ∈ global_spacetime_domain 3) :
    iteratedFDerivWithin ℝ n f (global_spacetime_domain 3) z =
      (iteratedFDerivWithin ℝ n
          (Function.uncurry (leanFieldToComparator f))
          nonnegativeTime (leanSpacetimeToPair z)).compContinuousLinearMap
        (fun _ => pairLeanSpacetimeContinuousLinearEquiv.symm.toContinuousLinearMap) := by
  have hpull :
      ContDiffOn ℝ ∞
        (Function.uncurry (leanFieldToComparator f)) nonnegativeTime :=
    contDiffOn_leanFieldToComparator hf
  have h := iteratedFDerivWithin_comparatorFieldToLean hpull n z hz
  rw [comparatorFieldToLean_leanFieldToComparator] at h
  exact h

theorem norm_iteratedFDerivWithin_leanField_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Spacetime3 → E}
    (hf : ContDiffOn ℝ ∞ f (global_spacetime_domain 3))
    (n : ℕ) (z : Spacetime3) (hz : z ∈ global_spacetime_domain 3) :
    ‖iteratedFDerivWithin ℝ n f (global_spacetime_domain 3) z‖ ≤
      ‖iteratedFDerivWithin ℝ n
          (Function.uncurry (leanFieldToComparator f))
          nonnegativeTime (leanSpacetimeToPair z)‖ *
        ‖pairLeanSpacetimeContinuousLinearEquiv.symm.toContinuousLinearMap‖ ^ n := by
  rw [iteratedFDerivWithin_leanField_eq_pullback hf n z hz]
  exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans_eq
    (by simp)

end DASHILiteralClayNS
