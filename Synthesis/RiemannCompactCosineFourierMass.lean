import Synthesis.RiemannCompactCosineFourthDerivative
import Zeta23Bridge.OscillatoryKernelDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Fourier.Inversion

/-!
# L1 Fourier-mass prerequisites for compact cosine profiles

For a real C^2 compactly-supported profile P, its cosine transform

  C_P(q) = ∫ P(u) cos(q u) du

is globally integrable.  The proof is deliberately elementary and reuses the
repository's oscillatory integration-by-parts owner:

* a uniform L1 bound near q=0;
* two integrations by parts giving O(q^-2) away from q=0;
* domination by a multiple of (1+q^2)^-1.

This is the exact prerequisite needed before invoking Mathlib Fourier
inversion to identify the total cosine mass with 2*pi*P(0).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Synthesis

open Zeta23Bridge.OscillatoryKernelDecay

def compactCosineSecondDerivativeMass
    (P : ℝ -> ℝ) : ℝ :=
  ∫ u : ℝ, |deriv (deriv P) u|

theorem compactCosineSecondDerivativeMass_nonneg
    (P : ℝ -> ℝ) :
    0 <= compactCosineSecondDerivativeMass P := by
  unfold compactCosineSecondDerivativeMass
  positivity

theorem compactCosineTransform_continuous
    {P : ℝ -> ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P) :
    Continuous (compactCosineTransform P) := by
  apply continuous_iff_continuousAt.2
  intro q
  exact (compactCosineTransform_hasDerivAt hP hPc q).continuousAt

theorem compactCosineTransform_abs_le_profileMass
    {P : ℝ -> ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (q : ℝ) :
    |compactCosineTransform P q|
      <= compactProfileAbsMoment P 0 := by
  have hi :
      Integrable (fun u : ℝ => P u * Real.cos (q*u)) :=
    (hP.mul (by fun_prop)).integrable_of_hasCompactSupport hPc.mul_right
  have hia :
      Integrable (fun u : ℝ => |P u|) :=
    hP.abs.integrable_of_hasCompactSupport hPc.abs
  unfold compactCosineTransform compactProfileAbsMoment
  calc
    |∫ u : ℝ, P u * Real.cos (q*u)|
      <= ∫ u : ℝ, |P u * Real.cos (q*u)| :=
        abs_integral_le_integral_abs
    _ <= ∫ u : ℝ, |P u| := by
      apply integral_mono hi.abs hia
      intro u
      rw [abs_mul]
      exact mul_le_of_le_one_right
        (abs_nonneg (P u)) (Real.abs_cos_le_one (q*u))
    _ = ∫ u : ℝ, |P u| * |u|^0 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by simp

theorem compactCosineTransform_abs_le_invSq
    {P : ℝ -> ℝ}
    (hP : ContDiff ℝ 2 P)
    (hPc : HasCompactSupport P)
    {q : ℝ}
    (hq : q ≠ 0) :
    |compactCosineTransform P q|
      <= compactCosineSecondDerivativeMass P / q^2 := by
  have hP1 : ContDiff ℝ 1 P := hP.of_le (by norm_num)
  have hPd1 : ContDiff ℝ 1 (deriv P) := ContDiff.deriv' hP
  have h1 := integral_mul_cos_eq hP1 hPc hq
  have h2 := integral_mul_sin_eq hPd1 hPc.deriv hq
  have hsecond :
      (∫ u : ℝ, P u * Real.cos (q*u))
        =
      -(1/q^2) *
        ∫ u : ℝ, deriv (deriv P) u * Real.cos (q*u) := by
    rw [h1,h2]
    field_simp [hq]
    ring
  have hd2c : Continuous (deriv (deriv P)) :=
    hPd1.continuous_deriv le_rfl
  have hd2s : HasCompactSupport (deriv (deriv P)) :=
    hPc.deriv.deriv
  have hi :
      Integrable
        (fun u : ℝ => deriv (deriv P) u * Real.cos (q*u)) :=
    Continuous.integrable_of_hasCompactSupport
      (hd2c.mul (by fun_prop)) hd2s.mul_right
  have hiabs :
      Integrable (fun u : ℝ => |deriv (deriv P) u|) :=
    hd2c.abs.integrable_of_hasCompactSupport hd2s.abs
  have hbound :
      |∫ u : ℝ, deriv (deriv P) u * Real.cos (q*u)|
        <= ∫ u : ℝ, |deriv (deriv P) u| := by
    calc
      |∫ u : ℝ, deriv (deriv P) u * Real.cos (q*u)|
        <=
      ∫ u : ℝ,
        |deriv (deriv P) u * Real.cos (q*u)| :=
          abs_integral_le_integral_abs
      _ <= ∫ u : ℝ, |deriv (deriv P) u| := by
        apply integral_mono hi.abs hiabs
        intro u
        rw [abs_mul]
        exact mul_le_of_le_one_right
          (abs_nonneg _) (Real.abs_cos_le_one _)
  unfold compactCosineTransform
  rw [hsecond, abs_mul, abs_neg,
      abs_of_nonneg (by positivity : 0 <= 1/q^2)]
  unfold compactCosineSecondDerivativeMass
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

theorem compactCosineTransform_integrable
    {P : ℝ -> ℝ}
    (hP : ContDiff ℝ 2 P)
    (hPc : HasCompactSupport P) :
    Integrable (compactCosineTransform P) := by
  let M0 : ℝ := compactProfileAbsMoment P 0
  let M2 : ℝ := compactCosineSecondDerivativeMass P
  let K : ℝ := 2 * (M0 + M2)
  have hPcont : Continuous P := hP.continuous
  have hM0 : 0 <= M0 := by
    dsimp [M0, compactProfileAbsMoment]
    positivity
  have hM2 : 0 <= M2 := by
    dsimp [M2]
    exact compactCosineSecondDerivativeMass_nonneg P
  have hK : 0 <= K := by
    dsimp [K]
    positivity
  have hmajor :
      ∀ q : ℝ,
        |compactCosineTransform P q|
          <= K * (1 + q^2)⁻¹ := by
    intro q
    have hmass :=
      compactCosineTransform_abs_le_profileMass hPcont hPc q
    by_cases hq : |q| <= 1
    · have hq2 : q^2 <= 1 := by
        nlinarith [sq_nonneg q]
      have hden : 0 < 1 + q^2 := by positivity
      have hhalf :
          (1/2 : ℝ) <= (1 + q^2)⁻¹ := by
        rw [le_inv_iff₀ hden]
        nlinarith
      dsimp [K]
      have hscale :=
        mul_le_mul_of_nonneg_left hhalf
          (by positivity : 0 <= 2*(M0+M2))
      nlinarith
    · have hqgt : 1 < |q| := lt_of_not_ge hq
      have hq0 : q ≠ 0 := by
        intro hz
        rw [hz, abs_zero] at hqgt
        linarith
      have hdec :=
        compactCosineTransform_abs_le_invSq hP hPc hq0
      have hq2 : 1 < q^2 := by
        nlinarith [sq_abs q]
      have hden : 0 < 1 + q^2 := by positivity
      have hinv :
          1 / q^2 <= 2 * (1 + q^2)⁻¹ := by
        rw [div_eq_mul_inv]
        have hq2pos : 0 < q^2 := by positivity
        rw [inv_le_iff₀ hq2pos]
        field_simp [ne_of_gt hden, ne_of_gt hq2pos]
        nlinarith
      dsimp [M2] at hdec
      dsimp [K]
      have hm :=
        mul_le_mul_of_nonneg_left hinv hM2
      calc
        |compactCosineTransform P q|
          <= M2 / q^2 := hdec
        _ <= 2*M2*(1+q^2)⁻¹ := by
          simpa [div_eq_mul_inv, mul_assoc] using hm
        _ <= 2*(M0+M2)*(1+q^2)⁻¹ := by
          have hweight : 0 <= (1+q^2)⁻¹ := by positivity
          nlinarith
  have hmajInt :
      Integrable (fun q : ℝ => K * (1+q^2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul K
  have hC :
      Continuous (compactCosineTransform P) :=
    compactCosineTransform_continuous hPcont hPc
  exact hmajInt.mono'
    hC.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs]
      have hkq : 0 <= K * (1+q^2)⁻¹ := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hkq]
      exact hmajor q)

end Synthesis
