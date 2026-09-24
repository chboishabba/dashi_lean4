import Synthesis.RiemannProjectiveZetaMuDerivativeTailDecay

/-!
# The theorem-bearing Abel correlation tail envelope

Combining:
* the arbitrary-endpoint Zeta23 discrepancy
    |E_A(x)| <= C (log(A+3)+log(x+4)),
* the exact physical derivative decay
    |phi_t'(x)| <= C'_t t/(x-t)^2,

gives the literal signed Abel integrand the pointwise envelope

  |phi_t'(x) E_A(x)|
    <= C'_t t/(x-t)^2
       * C (log(A+3)+log(x+4)).

This is the correct full-window tail majorant.  In ordinary analysis
log(x)/(x-t)^2 is integrable at +infinity, so the remaining improper-integral
passage is now a standard analytic compiler rather than a number-theoretic
estimate.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

theorem exists_projectiveZetaMu_correlation_tail_pointwise_bound :
    ∃ C T0 : ℝ, 0 ≤ C ∧
      ∀ t A x : ℝ,
        18 ≤ t ->
        max T0 4 ≤ A ->
        A < x ->
        x ≠ t ->
        |normalizedProjectiveOrdinateTestDeriv t x
          * zetaMuCumulativeDiscrepancy A x|
          ≤
        (normalizedProjectiveDerivativeCurvature t * t / (x-t)^2)
          *
        (C * (Real.log (A+3) + Real.log (x+4))) := by
  obtain ⟨C, T0, hC, hD⟩ :=
    exists_zetaMuWindowDiscrepancy_arbitrary_bound
  refine ⟨C, T0, hC, ?_⟩
  intro t A x ht hA hAx hxt
  have htpos : 0 < t := by linarith
  have hder :=
    normalizedProjectiveOrdinateTestDeriv_abs_le_gap_sq
      (t := t) (x := x) htpos hxt
  have hdisc :
      |zetaMuCumulativeDiscrepancy A x|
        ≤ C * (Real.log (A+3) + Real.log (x+4)) := by
    rw [zetaMuCumulativeDiscrepancy_endpoint]
    exact hD A x hA hAx
  have hfactor :
      0 ≤ normalizedProjectiveDerivativeCurvature t * t / (x-t)^2 := by
    have hcurv := normalizedProjectiveDerivativeCurvature_nonneg t
    positivity
  rw [abs_mul]
  exact mul_le_mul hder hdisc (abs_nonneg _) hfactor

end Synthesis
