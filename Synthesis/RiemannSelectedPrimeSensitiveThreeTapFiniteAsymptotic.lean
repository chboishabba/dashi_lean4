import Synthesis.RiemannSelectedPrimeSensitiveThreeTapM0Uniform
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapMaxCutScalarSplit

/-!
# Explicit finite one-scale asymptotic budget

The canonical normalized mass M0 is now uniformly bounded on every selected
signed-pole witness.  This file substitutes that bound into the half-height
finite budget, removing the abstract producer parameter M from Route A.

The remaining finite budget is

  U(eps) * Q(t;C,Cmu),

where

  U(eps) = 2592 cosh(1)^2 (1+2|eps|)^2.

A second theorem makes the log-over-t scale explicit without introducing any
limit machinery:

  Q(t;C,Cmu)
    <= (256 Cmu + 3328 C/5) * (2 log t + 1)/t

for t>=200 and nonnegative C,Cmu.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators Interval

/-- Uniform same-object bound for the canonical normalized transformed mass. -/
def threeTapUniformM0Bound (eps : ℝ) : ℝ :=
  2592 * (Real.cosh 1)^2 * (1 + 2*|eps|)^2

theorem threeTapUniformM0Bound_nonneg (eps : ℝ) :
    0 <= threeTapUniformM0Bound eps := by
  unfold threeTapUniformM0Bound
  positivity

theorem QuarticFourSignedPolePair.threeTapCanonicalM0_le_uniformBound
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapCanonicalM0 eps <= threeTapUniformM0Bound eps := by
  simpa [threeTapUniformM0Bound] using W.threeTapCanonicalM0_le_uniform ht (eps:=eps)

/-- Fully explicit finite half-height budget after closing M0. -/
def threeTapUniformFiniteHalfHeightBudget
    (t eps C Cmu : ℝ) : ℝ :=
  threeTapUniformM0Bound eps * threeTapHalfHeightLogCoefficient t C Cmu

/-- The actual log budget is controlled by the explicit witness-independent
finite budget. -/
theorem QuarticFourSignedPolePair.threeTapAdverseHalfHeightLogBudget_le_uniformFinite
    {t eps C Cmu : ℝ}
    (ht : 200 <= t)
    (hC : 0 <= C)
    (hCmu : 0 <= Cmu)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapAdverseHalfHeightLogBudget eps C Cmu
      <= threeTapUniformFiniteHalfHeightBudget t eps C Cmu := by
  unfold threeTapUniformFiniteHalfHeightBudget
  exact W.threeTapAdverseHalfHeightLogBudget_le_of_M0_le
    ht hC hCmu (W.threeTapCanonicalM0_le_uniformBound ht)

/-- The coefficient Q has an explicit O(log t/t) envelope.  This uses only
t>=200 and the nonnegativity of the unconditional RvM/mu constants. -/
theorem threeTapHalfHeightLogCoefficient_le_logOverT
    {t C Cmu : ℝ}
    (ht : 200 <= t)
    (hC : 0 <= C)
    (hCmu : 0 <= Cmu) :
    threeTapHalfHeightLogCoefficient t C Cmu
      <=
    (256*Cmu + (3328/5)*C) * ((2*Real.log t + 1)/t) := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 <= t := by linarith
  have hlog : 0 <= Real.log t := Real.log_nonneg ht1
  have hL : 0 <= 2*Real.log t + 1 := by linarith
  have hsmall : 1/t^2 <= 1/t := by
    have hinv : 0 <= 1/t := by positivity
    have hinvle : 1/t <= 1 := by
      rw [div_le_one ht0]
      exact ht1
    nlinarith
  unfold threeTapHalfHeightLogCoefficient
  have hmu :
      (256/t) * (Cmu * (Real.log t + 1))
        <= (256*Cmu) * ((2*Real.log t + 1)/t) := by
    have hlogpart : Real.log t + 1 <= 2*Real.log t + 1 := by linarith
    have hscale : 0 <= (256/t)*Cmu := by positivity
    calc
      (256/t) * (Cmu * (Real.log t + 1))
        = ((256/t)*Cmu) * (Real.log t+1) := by ring
      _ <= ((256/t)*Cmu) * (2*Real.log t+1) :=
        mul_le_mul_of_nonneg_left hlogpart hscale
      _ = (256*Cmu) * ((2*Real.log t+1)/t) := by ring
  have hrv2 :
      (256/t^2) * (C * (2*Real.log t + 1))
        <= (256*C) * ((2*Real.log t + 1)/t) := by
    have hs := mul_le_mul_of_nonneg_right hsmall
      (mul_nonneg hC hL)
    nlinarith
  have hrv1 :
      (2048/(5*t)) * (C * (2*Real.log t + 1))
        = ((2048/5)*C) * ((2*Real.log t + 1)/t) := by ring
  rw [hrv1]
  have hsum := add_le_add (add_le_add hmu hrv2) le_rfl
  calc
    (256/t) * (Cmu * (Real.log t + 1))
        + (256/t^2) * (C * (2*Real.log t + 1))
        + ((2048/5)*C) * ((2*Real.log t + 1)/t)
      <= (256*Cmu) * ((2*Real.log t + 1)/t)
        + (256*C) * ((2*Real.log t + 1)/t)
        + ((2048/5)*C) * ((2*Real.log t + 1)/t) := hsum
    _ = (256*Cmu + (3328/5)*C) * ((2*Real.log t + 1)/t) := by ring

/-- Explicit finite O(log t/t) envelope after closing the canonical mass. -/
theorem threeTapUniformFiniteHalfHeightBudget_le_logOverT
    {t eps C Cmu : ℝ}
    (ht : 200 <= t)
    (hC : 0 <= C)
    (hCmu : 0 <= Cmu) :
    threeTapUniformFiniteHalfHeightBudget t eps C Cmu
      <=
    threeTapUniformM0Bound eps
      * ((256*Cmu + (3328/5)*C) * ((2*Real.log t + 1)/t)) := by
  unfold threeTapUniformFiniteHalfHeightBudget
  exact mul_le_mul_of_nonneg_left
    (threeTapHalfHeightLogCoefficient_le_logOverT ht hC hCmu)
    (threeTapUniformM0Bound_nonneg eps)

/-- Route-A compiler with the finite mass parameter completely discharged.
The only remaining same-object analytic inputs are now the actual half-height
tail and the local-compensation floor. -/
theorem QuarticFourSignedPolePair.exists_threeTapHalfHeightUniformFinitePass_constants :
    ∃ C Cmu : ℝ, 0 <= C ∧ 0 <= Cmu ∧
      ∀ {t eps H : ℝ},
        200 <= t ->
        ∀ W : QuarticFourSignedPolePair t,
        threeTapUniformFiniteHalfHeightBudget t eps C Cmu <= H ->
        W.threeTapPairAdverseFarAfter eps (t/2) < H ->
        H <= W.threeTapAdaptiveLocalExact eps
            - W.threeTapResonanceCompensation eps ->
        W.threeTapResonancePaidCost eps < 0 := by
  obtain ⟨C,Cmu,hC,hCmu,hpass⟩ :=
    QuarticFourSignedPolePair.exists_threeTapHalfHeightSplitPass_constants
  refine ⟨C,Cmu,hC,hCmu,?_⟩
  intro t eps H ht W hfinite hfar hH
  apply hpass ht W
    (W.threeTapCanonicalM0_le_uniformBound ht)
  · simpa [threeTapUniformFiniteHalfHeightBudget] using hfinite
  · exact hfar
  · exact hH

end Synthesis
