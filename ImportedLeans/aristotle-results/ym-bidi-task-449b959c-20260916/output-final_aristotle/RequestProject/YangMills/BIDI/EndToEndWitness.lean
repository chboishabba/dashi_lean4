/-
# The end-to-end chain is not vacuous

`bidi_end_to_end` is an implication with many hypotheses; this file shows that
they can all be met simultaneously, so the implication has content.
-/
import Mathlib
import RequestProject.YangMills.BIDI.EndToEnd
import RequestProject.YangMills.BIDI.Witnesses

namespace RequestProject.YangMills.BIDI

open Filter Topology MeasureTheory
open RequestProject.YangMills.VacuumSectorSpectralGap
open RequestProject.YangMills.ContinuumGapTransport
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem end_to_end_nonvacuous (vac : E) (hunit : ‖vac‖ = 1) {m : ℝ} (hm : 0 < m)
    {lam : ℝ} (hlt : lam < m) {y : E} (hy : ⟪vac, y⟫_ℂ = 0) :
    (∃! psi : (projHam vac m).domain, ⟪vac, (psi : E)⟫_ℂ = 0 ∧
        (projHam vac m) psi - (lam : ℂ) • (psi : E) = y) ∧
      HasVacuumFormGap (projHam vac m) vac m := by
  have hnorm : ∀ psi : (projHam vac m).domain, ∀ t : ℝ,
      ‖((‖(psi : E)‖ ^ 2 * Real.exp (-(m * t)) : ℝ) : ℂ)‖
        = ‖(psi : E)‖ ^ 2 * Real.exp (-(m * t)) := by
    intro psi t
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine bidi_end_to_end hm
    (fun _ : ℕ => (clusteringWitness vac hm).toSpectralRepresentation)
    (fun _ psi t => ((‖(psi : E)‖ ^ 2 * Real.exp (-(m * t)) : ℝ) : ℂ))
    (fun _ psi => ‖(psi : E)‖ ^ 2) ?_ ?_ (isVacuumGraphLimit_const _ _)
    (isSelfAdjoint_projHam vac m) Submodule.mem_top hunit (projHam_vac vac m) hlt hy
  · intro _ psi _ t _
    rw [hnorm psi t]
    simp [clusteringWitness, diracSpectralMeasure, integral_smul_measure, smul_eq_mul,
      mul_comm]
  · intro _ psi t _
    exact le_of_eq (hnorm psi t)

end RequestProject.YangMills.BIDI
