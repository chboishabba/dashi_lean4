import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdverseCutoffOptimization

/-!
# Collapse the half-height finite core to one normalized M0 mass

The scale table still contains a first absolute moment M1.  The transformed
support itself removes that apparent extra degree of freedom:

  M1 <= supportRadius * M0.

For t>=200 the translated normalized support satisfies

  supportRadius < t/10.

Therefore every finite-core term at R=t/2 is controlled by the same canonical
M0 mass.  The resulting source-visible budget has the form

  M0 * [ O(log t / t) + O(log t / t^2) ],

with explicit coefficients and no hidden profile moment beyond M0.

This does not assert that M0 is uniformly bounded in t; that is intentionally
left as the next same-object analytic question.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators Interval

/-- First absolute moment is bounded by support radius times absolute mass. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMomentOne_le
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapNormalizedProjectiveAbsMoment eps 1
      <=
    W.threeTapNormalizedSupportRadius
      * W.threeTapNormalizedProjectiveAbsMass eps := by
  let P := W.threeTapNormalizedSignedProjectiveProfile eps
  have h1 := compactProfile_absMoment_integrable
    (W.threeTapNormalizedProjective_continuous (eps:=eps))
    (W.threeTapNormalizedProjective_compact (eps:=eps)) 1
  have h0 := compactProfile_absMoment_integrable
    (W.threeTapNormalizedProjective_continuous (eps:=eps))
    (W.threeTapNormalizedProjective_compact (eps:=eps)) 0
  unfold QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMoment
    QuarticFourSignedPolePair.threeTapNormalizedProjectiveAbsMass
    compactProfileAbsMoment
  calc
    (∫ v : ℝ, |P v| * |v|^1)
      <=
    ∫ v : ℝ,
      W.threeTapNormalizedSupportRadius * (|P v| * |v|^0) := by
        apply integral_mono h1 (h0.const_mul _)
        intro v
        by_cases hv : P v = 0
        · simp [hv]
        · have hs := W.threeTapNormalizedSignedProjective_support hv
          have hP : 0 <= |P v| := abs_nonneg _
          simp only [pow_one, pow_zero, mul_one]
          nlinarith
    _ = W.threeTapNormalizedSupportRadius *
        (∫ v : ℝ, |P v| * |v|^0) := by
      rw [integral_const_mul]
    _ = _ := by rfl

/-- In the high-t regime the O(t) translated support has the explicit bound
t/10. -/
theorem QuarticFourSignedPolePair.threeTapNormalizedSupportRadius_lt_tenth
    {t : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapNormalizedSupportRadius < t/10 := by
  have ht0 : 0 < t := by linarith
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos
      (show (0 : ℝ) < 2 by norm_num)
      (show (2 : ℝ) ≠ 1 by norm_num)
    norm_num at h ⊢
    exact h
  have hshift : 0 < threeTapNormalizedShift t (Real.log 2) := by
    unfold threeTapNormalizedShift
    positivity
  have hmul : (t/16) * Real.log 2 < t/16 :=
    mul_lt_mul_of_pos_left hlog (by positivity)
  unfold QuarticFourSignedPolePair.threeTapNormalizedSupportRadius
    threeTapNormalizedShift
  rw [abs_of_pos hshift]
  nlinarith

/-- Consequently the canonical cosh-weighted M1 is bounded by t/10 times the
canonical cosh-weighted M0. -/
theorem QuarticFourSignedPolePair.threeTapCanonicalM1_le_tenth_mul_M0
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapCanonicalM1 eps
      <= (t/10) * W.threeTapCanonicalM0 eps := by
  have h1 := W.threeTapNormalizedProjectiveAbsMomentOne_le (eps:=eps)
  have hs := (W.threeTapNormalizedSupportRadius_lt_tenth ht).le
  have hM0 : 0 <= W.threeTapNormalizedProjectiveAbsMass eps :=
    W.threeTapNormalizedProjectiveAbsMoment_nonneg (eps:=eps) 0
  have hcosh : 0 <= Real.cosh 1 := (Real.cosh_pos _).le
  unfold QuarticFourSignedPolePair.threeTapCanonicalM0
    QuarticFourSignedPolePair.threeTapCanonicalM1
  calc
    Real.cosh 1 * W.threeTapNormalizedProjectiveAbsMoment eps 1
      <= Real.cosh 1 *
        (W.threeTapNormalizedSupportRadius
          * W.threeTapNormalizedProjectiveAbsMass eps) :=
      mul_le_mul_of_nonneg_left h1 hcosh
    _ <= Real.cosh 1 *
        ((t/10) * W.threeTapNormalizedProjectiveAbsMass eps) := by
      gcongr
    _ = (t/10) *
        (Real.cosh 1 * W.threeTapNormalizedProjectiveAbsMass eps) := by ring

/-- Half-height budget after eliminating M1 in favor of M0. -/
def QuarticFourSignedPolePair.threeTapAdverseHalfHeightM0Budget
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps C Cmu : ℝ) : ℝ :=
  let E := threeTapHalfHeightRvMFactor t C
  let U := threeTapHalfHeightMuFactor t Cmu
  let M0 := W.threeTapCanonicalM0 eps
  (256/t) * M0 * U
    + (256/t^2) * E * M0
    + (2048/(5*t)) * E * M0

/-- The closed scale budget is bounded by the one-mass M0 budget. -/
theorem QuarticFourSignedPolePair.threeTapAdverseHalfHeightClosedBudget_le_M0Budget
    {t eps C Cmu : ℝ}
    (ht : 200 <= t)
    (hC : 0 <= C)
    (hCmu : 0 <= Cmu)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapAdverseHalfHeightClosedBudget eps C Cmu
      <= W.threeTapAdverseHalfHeightM0Budget eps C Cmu := by
  have ht0 : 0 < t := by linarith
  have hM1 := W.threeTapCanonicalM1_le_tenth_mul_M0 ht (eps:=eps)
  have hE : 0 <= threeTapHalfHeightRvMFactor t C := by
    unfold threeTapHalfHeightRvMFactor
    have h1 : 0 <= Real.log (t/2+3) := Real.log_nonneg (by linarith)
    have h2 : 0 <= Real.log (3*t/2+4) := Real.log_nonneg (by linarith)
    exact mul_nonneg hC (add_nonneg h1 h2)
  have hcoef : 0 <= (4096/t^2) * threeTapHalfHeightRvMFactor t C := by
    positivity
  have hlast := mul_le_mul_of_nonneg_left hM1 hcoef
  unfold QuarticFourSignedPolePair.threeTapAdverseHalfHeightClosedBudget
    QuarticFourSignedPolePair.threeTapAdverseHalfHeightM0Budget
  dsimp
  have heq :
      (4096/t^2) * threeTapHalfHeightRvMFactor t C
          * ((t/10) * W.threeTapCanonicalM0 eps)
        =
      (2048/(5*t)) * threeTapHalfHeightRvMFactor t C
          * W.threeTapCanonicalM0 eps := by
    field_simp [ne_of_gt ht0]
    ring
  rw [heq] at hlast
  linarith

/-- A simpler logarithmic envelope for the two half-height RvM factors. -/
theorem threeTapHalfHeightRvMFactor_le_logEnvelope
    {t C : ℝ}
    (ht : 200 <= t)
    (hC : 0 <= C) :
    threeTapHalfHeightRvMFactor t C
      <= C * (2 * Real.log t + 1) := by
  have ht0 : 0 < t := by linarith
  have hlog2 : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos
      (show (0 : ℝ) < 2 by norm_num)
      (show (2 : ℝ) ≠ 1 by norm_num)
    norm_num at h ⊢
    exact h
  have h1 : Real.log (t/2+3) <= Real.log t :=
    Real.log_le_log (by linarith) (by linarith)
  have h2raw : Real.log (3*t/2+4) <= Real.log (2*t) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlogmul : Real.log (2*t) = Real.log 2 + Real.log t := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt ht0)]
  have h2 : Real.log (3*t/2+4) <= Real.log t + 1 := by
    rw [hlogmul] at h2raw
    linarith
  unfold threeTapHalfHeightRvMFactor
  have hadd :
      Real.log (t/2+3) + Real.log (3*t/2+4)
        <= 2 * Real.log t + 1 := by linarith
  exact mul_le_mul_of_nonneg_left hadd hC

/-- Corresponding logarithmic envelope for the smooth-mu factor. -/
theorem threeTapHalfHeightMuFactor_le_logEnvelope
    {t Cmu : ℝ}
    (ht : 200 <= t)
    (hCmu : 0 <= Cmu) :
    threeTapHalfHeightMuFactor t Cmu
      <= Cmu * (Real.log t + 1) := by
  have ht0 : 0 < t := by linarith
  have hlog2 : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos
      (show (0 : ℝ) < 2 by norm_num)
      (show (2 : ℝ) ≠ 1 by norm_num)
    norm_num at h ⊢
    exact h
  have hraw : Real.log (3*t/2+3) <= Real.log (2*t) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlogmul : Real.log (2*t) = Real.log 2 + Real.log t := by
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt ht0)]
  rw [hlogmul] at hraw
  unfold threeTapHalfHeightMuFactor
  exact mul_le_mul_of_nonneg_left (by linarith) hCmu

/-- Fully explicit log-over-t finite-core envelope depending only on canonical
M0.  This is the quantitative object to compare with compensation and the
actual half-height far tail. -/
def QuarticFourSignedPolePair.threeTapAdverseHalfHeightLogBudget
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps C Cmu : ℝ) : ℝ :=
  let M0 := W.threeTapCanonicalM0 eps
  (256/t) * M0 * (Cmu * (Real.log t + 1))
    + (256/t^2) * (C * (2*Real.log t + 1)) * M0
    + (2048/(5*t)) * (C * (2*Real.log t + 1)) * M0

/-- The one-mass budget is bounded by the explicit logarithmic envelope. -/
theorem QuarticFourSignedPolePair.threeTapAdverseHalfHeightM0Budget_le_logBudget
    {t eps C Cmu : ℝ}
    (ht : 200 <= t)
    (hC : 0 <= C)
    (hCmu : 0 <= Cmu)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapAdverseHalfHeightM0Budget eps C Cmu
      <= W.threeTapAdverseHalfHeightLogBudget eps C Cmu := by
  have ht0 : 0 < t := by linarith
  have hE := threeTapHalfHeightRvMFactor_le_logEnvelope ht hC
  have hU := threeTapHalfHeightMuFactor_le_logEnvelope ht hCmu
  have hM0 : 0 <= W.threeTapCanonicalM0 eps := by
    unfold QuarticFourSignedPolePair.threeTapCanonicalM0
    exact mul_nonneg (Real.cosh_pos _).le
      (W.threeTapNormalizedProjectiveAbsMoment_nonneg (eps:=eps) 0)
  have h256t : 0 <= 256/t := by positivity
  have h256t2 : 0 <= 256/t^2 := by positivity
  have h2048 : 0 <= 2048/(5*t) := by positivity
  unfold QuarticFourSignedPolePair.threeTapAdverseHalfHeightM0Budget
    QuarticFourSignedPolePair.threeTapAdverseHalfHeightLogBudget
  dsimp
  exact add_le_add
    (add_le_add
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hU hM0) h256t)
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hE hM0) h256t2))
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hE hM0) h2048)

/-- Entire finite half-height scale budget is bounded by the explicit M0
log-over-t envelope. -/
theorem QuarticFourSignedPolePair.threeTapAdverseHalfHeightClosedBudget_le_logBudget
    {t eps C Cmu : ℝ}
    (ht : 200 <= t)
    (hC : 0 <= C)
    (hCmu : 0 <= Cmu)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapAdverseHalfHeightClosedBudget eps C Cmu
      <= W.threeTapAdverseHalfHeightLogBudget eps C Cmu :=
  (W.threeTapAdverseHalfHeightClosedBudget_le_M0Budget ht hC hCmu).trans
    (W.threeTapAdverseHalfHeightM0Budget_le_logBudget ht hC hCmu)

end Synthesis
