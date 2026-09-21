import Synthesis.RiemannNormalizedProjectiveBaseLocalSign
import Synthesis.RiemannProjectiveZetaMuContinuousAbel

/-!
# Local radial discrepancy criterion for the projective Abel consumer

For the canonical projective test, positive curvature forces the derivative to
point away from the target ordinate in a punctured neighbourhood:

  sign phi_t'(x) = sign (x-t).

Hence the Abel correlation term

  phi_t'(x) * E_A(x)

is nonnegative there whenever the literal cumulative discrepancy itself points
radially away from the target,

  (x-t) * E_A(x) >= 0.

This is the sharp local number-theoretic condition behind the signed Route A.
It is substantially stronger than an absolute Backlund/RvM bound and is not
proved here; this file proves that it is exactly sufficient for the local Abel
sign.

The final lemmas also package the algebraic finite-window criterion:

  endpoint <= 0 and correlation integral >= 0
    => projective N-mu residual <= 0.

No absolute values enter.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval Real

namespace Synthesis

/--
Near the target ordinate, radial sign of the cumulative discrepancy implies
nonnegative projective Abel correlation pointwise.
-/
theorem exists_projectiveOrdinateTestDeriv_discrepancy_radial_criterion
    {t : ℝ} (ht : 18 ≤ t) :
    ∃ eps : ℝ, 0 < eps ∧
      ∀ A x : ℝ,
        0 < |(x - t) / t| →
        |(x - t) / t| < eps →
        0 ≤ (x - t) * zetaMuCumulativeDiscrepancy A x →
        0 ≤
          normalizedProjectiveOrdinateTestDeriv t x
            * zetaMuCumulativeDiscrepancy A x := by
  obtain ⟨eps, heps, hpos, hneg⟩ :=
    exists_normalizedProjectiveBaseTransformDeriv_sign_punctured ht
  refine ⟨eps, heps, ?_⟩
  intro A x hq0 hqeps hrad
  have htpos : 0 < t := by linarith
  let q : ℝ := (x - t) / t
  have hqdef : q = (x - t) / t := rfl
  have hqne : q ≠ 0 := by
    intro hz
    apply (ne_of_gt hq0)
    simp [q, hz]
  by_cases hqx : 0 < q
  · have hderq : 0 < normalizedProjectiveBaseTransformDeriv t q := by
      apply hpos q hqx
      simpa [q] using hqeps
    have hxt : 0 < x - t := by
      have := (div_pos_iff.mp hqx)
      rcases this with h | h
      · exact h.1
      · exfalso
        linarith
    have hD : 0 ≤ zetaMuCumulativeDiscrepancy A x := by
      by_contra h
      have hDneg : zetaMuCumulativeDiscrepancy A x < 0 := lt_of_not_ge h
      have := mul_neg_of_pos_of_neg hxt hDneg
      linarith
    unfold normalizedProjectiveOrdinateTestDeriv
    have hcoef : 0 < 1 / t := one_div_pos.mpr htpos
    have hderphys :
        0 < (1 / t) * normalizedProjectiveBaseTransformDeriv t ((x-t)/t) := by
      simpa [q] using mul_pos hcoef hderq
    exact mul_nonneg hderphys.le hD
  · have hqneg : q < 0 := lt_of_le_of_ne (le_of_not_gt hqx) (Ne.symm hqne)
    have hqlo : -eps < q := by
      have habs : |q| = -q := abs_of_neg hqneg
      have := hqeps
      rw [← hqdef, habs] at this
      linarith
    have hderq : normalizedProjectiveBaseTransformDeriv t q < 0 :=
      hneg q hqlo hqneg
    have hxt : x - t < 0 := by
      have := (div_neg_iff.mp hqneg)
      rcases this with h | h
      · exact h.1
      · exfalso
        linarith
    have hD : zetaMuCumulativeDiscrepancy A x ≤ 0 := by
      by_contra h
      have hDpos : 0 < zetaMuCumulativeDiscrepancy A x := lt_of_not_ge h
      have := mul_neg_of_neg_of_pos hxt hDpos
      linarith
    unfold normalizedProjectiveOrdinateTestDeriv
    have hcoef : 0 < 1 / t := one_div_pos.mpr htpos
    have hderphys :
        (1 / t) * normalizedProjectiveBaseTransformDeriv t ((x-t)/t) < 0 := by
      simpa [q] using mul_neg_of_pos_of_neg hcoef hderq
    exact mul_nonneg_of_nonpos_of_nonpos hderphys.le hD

/--
Finite-window signed Abel compiler.  If the endpoint contribution is
nonpositive and the correlation integral is nonnegative, the exact projective
N-mu residual is nonpositive.
-/
theorem projectiveZetaMuWindowResidual_nonpos_of_signedAbel
    {t A B : ℝ}
    (ht : t ≠ 0)
    (hAB : A ≤ B)
    (hend :
      normalizedProjectiveOrdinateTest t B
          * zetaMuCumulativeDiscrepancy A B ≤ 0)
    (hcorr :
      0 ≤
        ∫ x in A..B,
          normalizedProjectiveOrdinateTestDeriv t x
            * zetaMuCumulativeDiscrepancy A x) :
    projectiveZetaMuWindowResidual t A B ≤ 0 := by
  rw [projectiveZetaMuWindowResidual_eq_discrepancyAbel ht hAB]
  linarith

/--
Strict version: a strictly negative endpoint or a strictly positive correlation
integral yields a strictly negative projective N-mu window residual.
-/
theorem projectiveZetaMuWindowResidual_neg_of_signedAbel
    {t A B : ℝ}
    (ht : t ≠ 0)
    (hAB : A ≤ B)
    (hend :
      normalizedProjectiveOrdinateTest t B
          * zetaMuCumulativeDiscrepancy A B ≤ 0)
    (hcorr :
      0 <
        ∫ x in A..B,
          normalizedProjectiveOrdinateTestDeriv t x
            * zetaMuCumulativeDiscrepancy A x) :
    projectiveZetaMuWindowResidual t A B < 0 := by
  rw [projectiveZetaMuWindowResidual_eq_discrepancyAbel ht hAB]
  linarith

end Synthesis
