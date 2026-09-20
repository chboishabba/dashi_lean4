import Synthesis.RiemannProjectiveZetaMuContinuousAbel
import Synthesis.RiemannNormalizedProjectiveProfileScaling

/-!
# Explicit inverse-t bound for the continuous projective N-mu window residual

The exact continuous Abel theorem bounds the literal projective base pairing by

  Dmax(A,B) * (M0(t) + ((B-A)/t) M1(t)),

where Dmax is the theorem-bearing Zeta23 cumulative N-mu discrepancy and M0,M1
are the L1 mass and first moment of the exact projective physical profile.

The canonical profile scaling theorem gives

  M0(t) <= K/t,
  M1(t) <= R K/t,

with
  K = 8 * normalizedCanonicalProfileMassUpper^2,
  R = 9*pi/4.

Therefore

  |R_proj(t;A,B)|
    <= Dmax(A,B) * (K/t) * (1 + R*(B-A)/t).

This is still an absolute estimate and hence is not by itself a near-line RH
closure.  Its purpose is to expose the actual t-scaling of the exact N-mu
consumer before the external reflection-pair factor 1/(2t) is applied.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

def normalizedProjectiveProfileScaleConstant : ℝ :=
  8 * normalizedCanonicalProfileMassUpper ^ 2

def normalizedProjectiveSupportRadius : ℝ :=
  9 * Real.pi / 4

theorem normalizedProjectiveProfileScaleConstant_nonneg :
    0 ≤ normalizedProjectiveProfileScaleConstant := by
  unfold normalizedProjectiveProfileScaleConstant
  positivity

theorem normalizedProjectiveSupportRadius_pos :
    0 < normalizedProjectiveSupportRadius := by
  unfold normalizedProjectiveSupportRadius
  positivity

theorem normalizedProjectiveProfileL1_le_scale_div_t
    {t : ℝ} (ht : 18 ≤ t) :
    normalizedProjectiveProfileL1 t
      ≤ normalizedProjectiveProfileScaleConstant / t := by
  simpa [normalizedProjectiveProfileScaleConstant] using
    normalizedProjectiveProfileL1_le_inv_t ht

theorem normalizedProjectiveProfileFirstMoment_le_scale_div_t
    {t : ℝ} (ht : 18 ≤ t) :
    normalizedProjectiveProfileFirstMoment t
      ≤ normalizedProjectiveSupportRadius
        * normalizedProjectiveProfileScaleConstant / t := by
  simpa [normalizedProjectiveSupportRadius,
    normalizedProjectiveProfileScaleConstant, mul_div_assoc] using
    normalizedProjectiveProfileFirstMoment_le_inv_t ht

theorem exists_projectiveZetaMuWindowResidual_explicit_inv_t_bound :
    ∃ C T0 : ℝ, 0 ≤ C ∧
      ∀ t A B : ℝ,
        18 ≤ t ->
        max T0 4 ≤ A ->
        A < B ->
        |projectiveZetaMuWindowResidual t A B|
          ≤
        (C * (Real.log (A + 3) + Real.log (B + 4)))
          *
        (normalizedProjectiveProfileScaleConstant / t)
          *
        (1 + normalizedProjectiveSupportRadius * ((B - A) / t)) := by
  obtain ⟨C, T0, hC, hbase⟩ :=
    exists_projectiveZetaMuWindowResidual_bound
  refine ⟨C, T0, hC, ?_⟩
  intro t A B ht hA hAB
  have ht0 : 0 < t := by linarith
  have hraw := hbase t A B ht0 hA hAB
  have hM0 :=
    normalizedProjectiveProfileL1_le_scale_div_t ht
  have hM1 :=
    normalizedProjectiveProfileFirstMoment_le_scale_div_t ht
  have hBA : 0 ≤ (B-A)/t := by
    exact div_nonneg (sub_nonneg.mpr hAB.le) ht0.le
  have hscale0 :
      0 ≤ normalizedProjectiveProfileScaleConstant / t := by
    exact div_nonneg normalizedProjectiveProfileScaleConstant_nonneg ht0.le
  have hsum :
      normalizedProjectiveProfileL1 t
        + ((B-A)/t) * normalizedProjectiveProfileFirstMoment t
      ≤
      (normalizedProjectiveProfileScaleConstant / t)
        *
      (1 + normalizedProjectiveSupportRadius * ((B-A)/t)) := by
    have h1 :=
      mul_le_mul_of_nonneg_left hM1 hBA
    calc
      normalizedProjectiveProfileL1 t
          + ((B-A)/t) * normalizedProjectiveProfileFirstMoment t
        ≤
      normalizedProjectiveProfileScaleConstant / t
          + ((B-A)/t)
            * (normalizedProjectiveSupportRadius
              * normalizedProjectiveProfileScaleConstant / t) :=
        add_le_add hM0 h1
      _ =
      (normalizedProjectiveProfileScaleConstant / t)
        *
      (1 + normalizedProjectiveSupportRadius * ((B-A)/t)) := by
        ring
  have hlogA : 0 ≤ Real.log (A+3) := by
    apply Real.log_nonneg
    have hA4 : 4 ≤ A := (le_max_right T0 4).trans hA
    linarith
  have hlogB : 0 ≤ Real.log (B+4) := by
    apply Real.log_nonneg
    have hA4 : 4 ≤ A := (le_max_right T0 4).trans hA
    linarith
  have hD :
      0 ≤ C * (Real.log (A+3) + Real.log (B+4)) := by
    positivity
  exact hraw.trans
    (mul_le_mul_of_nonneg_left hsum hD)

end Synthesis
