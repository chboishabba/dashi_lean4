/-
# Quadratic decay of the signed reflection-pair kernel in the ordinate gap

The signed carrier produced by `LiteralWeilOffOrdinateReflectionSymmetrization`
is a sum, over the literal off-ordinate zeros, of oscillatory integrals

    ∫ 4 g(u) cosh(a_ρ u) cos((Im ρ − t) u) du.

Any estimate that first takes absolute values inside the integral throws the
oscillation away and produces a bound with no decay in the ordinate gap
`δ = Im ρ − t`.  This module supplies the missing exact tool: for a compactly
supported `C²` weight, two integrations by parts give

    |∫ w(u) cos(δ u) du| ≤ ‖w''‖₁ / δ².

Everything is proved from scratch:

* `integral_deriv_eq_zero_of_hasCompactSupport` — the fundamental theorem of
  calculus on the whole line for a compactly supported `C¹` function;
* `integral_mul_cos_eq` / `integral_mul_sin_eq` — the two integration-by-parts
  identities against `cos(δ·)` and `sin(δ·)`;
* `integral_mul_cos_eq_second_order` — the exact second-order identity
  `∫ w cos(δ·) = −(1/δ²) ∫ w'' cos(δ·)`;
* `abs_integral_mul_cos_le` — the resulting quadratic decay bound.

The last statement is the analytic input the signed zero-tail estimate needs:
per-zero responses decay like `δ⁻²` in the ordinate gap, so the tail is
controlled by a convergent sum rather than by a positive scalar majorant.

No `sorry`, no `axiom`, no Boolean receipt, no numerical evidence.
-/
import Mathlib

noncomputable section

open MeasureTheory intervalIntegral

namespace Zeta23Bridge
namespace OscillatoryKernelDecay

/-! ## The integral of a derivative of a compactly supported function vanishes -/

theorem integral_deriv_eq_zero_of_hasCompactSupport {h : ℝ → ℝ}
    (h1 : ContDiff ℝ 1 h) (hc : HasCompactSupport h) :
    ∫ u : ℝ, deriv h u = 0 := by
  obtain ⟨R, hR⟩ := (hc.isCompact.isBounded).subset_closedBall (0 : ℝ)
  set M : ℝ := |R| + 1 with hM
  have hMpos : 0 < M := by positivity
  have houts : ∀ x : ℝ, M ≤ |x| → x ∉ tsupport h := by
    intro x hx hmem
    have hxR := hR hmem
    simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hxR
    have : |x| ≤ |R| := le_trans hxR (le_abs_self R)
    simp only [hM] at hx
    linarith
  have hzeroh : ∀ x : ℝ, M ≤ |x| → h x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (houts x hx)
  have hzerod : ∀ x : ℝ, M ≤ |x| → deriv h x = 0 := by
    intro x hx
    by_contra hne
    exact houts x hx (support_deriv_subset (by simpa [Function.mem_support] using hne))
  have hcompl : ∀ x ∉ Set.Icc (-M) M, deriv h x = 0 := by
    intro x hx
    apply hzerod
    simp only [Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with h' | h'
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  have hcont : Continuous (deriv h) := h1.continuous_deriv le_rfl
  calc ∫ u : ℝ, deriv h u = ∫ u in Set.Icc (-M) M, deriv h u :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hcompl).symm
    _ = ∫ u in Set.Ioc (-M) M, deriv h u := integral_Icc_eq_integral_Ioc
    _ = ∫ u in (-M)..M, deriv h u := (integral_of_le (by linarith)).symm
    _ = h M - h (-M) :=
        integral_deriv_eq_sub (fun x _ => (h1.differentiable one_ne_zero).differentiableAt)
          (hcont.intervalIntegrable _ _)
    _ = 0 := by
        rw [hzeroh M (by rw [abs_of_nonneg hMpos.le]),
          hzeroh (-M) (by rw [abs_neg, abs_of_nonneg hMpos.le])]
        ring

/-! ## Derivatives of the oscillating factors -/

theorem hasDerivAt_sin_mul (δ u : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sin (δ * x)) (Real.cos (δ * u) * δ) u := by
  have h : HasDerivAt (fun x : ℝ => δ * x) δ u := by
    simpa using (hasDerivAt_id u).const_mul δ
  simpa using h.sin

theorem hasDerivAt_cos_mul (δ u : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (δ * x)) (-Real.sin (δ * u) * δ) u := by
  have h : HasDerivAt (fun x : ℝ => δ * x) δ u := by
    simpa using (hasDerivAt_id u).const_mul δ
  simpa using h.cos

/-! ## The two integration-by-parts identities -/

theorem integral_mul_cos_eq {w : ℝ → ℝ} (hw : ContDiff ℝ 1 w) (hc : HasCompactSupport w)
    {δ : ℝ} (hδ : δ ≠ 0) :
    ∫ u : ℝ, w u * Real.cos (δ * u)
      = -(1 / δ) * ∫ u : ℝ, deriv w u * Real.sin (δ * u) := by
  set h : ℝ → ℝ := fun u => (w u * Real.sin (δ * u)) * (1 / δ) with hh
  have hdw : ∀ u, HasDerivAt w (deriv w u) u := fun u =>
    (hw.differentiable one_ne_zero).differentiableAt.hasDerivAt
  have hderiv : ∀ u, HasDerivAt h
      ((1 / δ) * (deriv w u * Real.sin (δ * u)) + w u * Real.cos (δ * u)) u := by
    intro u
    have hp : HasDerivAt (fun x : ℝ => w x * Real.sin (δ * x))
        (deriv w u * Real.sin (δ * u) + w u * (Real.cos (δ * u) * δ)) u :=
      (hdw u).mul (hasDerivAt_sin_mul δ u)
    have hq := hp.mul_const (1 / δ)
    have heq : (deriv w u * Real.sin (δ * u) + w u * (Real.cos (δ * u) * δ)) * (1 / δ)
        = (1 / δ) * (deriv w u * Real.sin (δ * u)) + w u * Real.cos (δ * u) := by
      field_simp
    rwa [heq] at hq
  have hderiv_eq : ∀ u, deriv h u
      = (1 / δ) * (deriv w u * Real.sin (δ * u)) + w u * Real.cos (δ * u) :=
    fun u => (hderiv u).deriv
  have hC1 : ContDiff ℝ 1 h := (hw.mul (by fun_prop)).mul contDiff_const
  have hCS : HasCompactSupport h :=
    HasCompactSupport.mul_right (HasCompactSupport.mul_right hc)
  have hzero := integral_deriv_eq_zero_of_hasCompactSupport hC1 hCS
  rw [funext hderiv_eq] at hzero
  have hi1 : Integrable (fun u : ℝ => (1 / δ) * (deriv w u * Real.sin (δ * u))) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact continuous_const.mul ((hw.continuous_deriv le_rfl).mul (by fun_prop))
    · exact HasCompactSupport.mul_left (hc.deriv.mul_right)
  have hi2 : Integrable (fun u : ℝ => w u * Real.cos (δ * u)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hw.continuous.mul (by fun_prop)
    · exact hc.mul_right
  rw [MeasureTheory.integral_add hi1 hi2, MeasureTheory.integral_const_mul] at hzero
  linarith [hzero]

theorem integral_mul_sin_eq {v : ℝ → ℝ} (hv : ContDiff ℝ 1 v) (hc : HasCompactSupport v)
    {δ : ℝ} (hδ : δ ≠ 0) :
    ∫ u : ℝ, v u * Real.sin (δ * u)
      = (1 / δ) * ∫ u : ℝ, deriv v u * Real.cos (δ * u) := by
  set h : ℝ → ℝ := fun u => (v u * Real.cos (δ * u)) * (-(1 / δ)) with hh
  have hdv : ∀ u, HasDerivAt v (deriv v u) u := fun u =>
    (hv.differentiable one_ne_zero).differentiableAt.hasDerivAt
  have hderiv : ∀ u, HasDerivAt h
      (-(1 / δ) * (deriv v u * Real.cos (δ * u)) + v u * Real.sin (δ * u)) u := by
    intro u
    have hp : HasDerivAt (fun x : ℝ => v x * Real.cos (δ * x))
        (deriv v u * Real.cos (δ * u) + v u * (-Real.sin (δ * u) * δ)) u :=
      (hdv u).mul (hasDerivAt_cos_mul δ u)
    have hq := hp.mul_const (-(1 / δ))
    have heq : (deriv v u * Real.cos (δ * u) + v u * (-Real.sin (δ * u) * δ)) * (-(1 / δ))
        = -(1 / δ) * (deriv v u * Real.cos (δ * u)) + v u * Real.sin (δ * u) := by
      field_simp
      ring
    rwa [heq] at hq
  have hderiv_eq : ∀ u, deriv h u
      = -(1 / δ) * (deriv v u * Real.cos (δ * u)) + v u * Real.sin (δ * u) :=
    fun u => (hderiv u).deriv
  have hC1 : ContDiff ℝ 1 h := (hv.mul (by fun_prop)).mul contDiff_const
  have hCS : HasCompactSupport h :=
    HasCompactSupport.mul_right (HasCompactSupport.mul_right hc)
  have hzero := integral_deriv_eq_zero_of_hasCompactSupport hC1 hCS
  rw [funext hderiv_eq] at hzero
  have hi1 : Integrable (fun u : ℝ => -(1 / δ) * (deriv v u * Real.cos (δ * u))) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact continuous_const.mul ((hv.continuous_deriv le_rfl).mul (by fun_prop))
    · exact HasCompactSupport.mul_left (hc.deriv.mul_right)
  have hi2 : Integrable (fun u : ℝ => v u * Real.sin (δ * u)) := by
    apply Continuous.integrable_of_hasCompactSupport
    · exact hv.continuous.mul (by fun_prop)
    · exact hc.mul_right
  rw [MeasureTheory.integral_add hi1 hi2, MeasureTheory.integral_const_mul] at hzero
  linarith [hzero]

/-! ## The exact second-order identity and the decay bound -/

/-- **Two exact integrations by parts.**  No absolute value has been taken. -/
theorem integral_mul_cos_eq_second_order {w : ℝ → ℝ}
    (hw : ContDiff ℝ 2 w) (hc : HasCompactSupport w) {δ : ℝ} (hδ : δ ≠ 0) :
    ∫ u : ℝ, w u * Real.cos (δ * u)
      = -(1 / δ ^ 2) * ∫ u : ℝ, deriv (deriv w) u * Real.cos (δ * u) := by
  have hw1 : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have hd1 : ContDiff ℝ 1 (deriv w) := ContDiff.deriv' hw
  have hstep1 := integral_mul_cos_eq hw1 hc hδ
  have hstep2 := integral_mul_sin_eq hd1 hc.deriv hδ
  rw [hstep1, hstep2]
  field_simp

/-- **Quadratic decay in the ordinate gap.** -/
theorem abs_integral_mul_cos_le {w : ℝ → ℝ}
    (hw : ContDiff ℝ 2 w) (hc : HasCompactSupport w) {δ : ℝ} (hδ : δ ≠ 0) :
    |∫ u : ℝ, w u * Real.cos (δ * u)| ≤ (∫ u : ℝ, |deriv (deriv w) u|) / δ ^ 2 := by
  have hd2c : Continuous (deriv (deriv w)) := (ContDiff.deriv' hw).continuous_deriv le_rfl
  have hd2s : HasCompactSupport (deriv (deriv w)) := hc.deriv.deriv
  have hiabs : Integrable (fun u : ℝ => |deriv (deriv w) u|) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop) (hd2s.abs)
  have hi : Integrable (fun u : ℝ => deriv (deriv w) u * Real.cos (δ * u)) :=
    Continuous.integrable_of_hasCompactSupport (hd2c.mul (by fun_prop)) hd2s.mul_right
  have hbound : |∫ u : ℝ, deriv (deriv w) u * Real.cos (δ * u)|
      ≤ ∫ u : ℝ, |deriv (deriv w) u| := by
    calc |∫ u : ℝ, deriv (deriv w) u * Real.cos (δ * u)|
        ≤ ∫ u : ℝ, |deriv (deriv w) u * Real.cos (δ * u)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ u : ℝ, |deriv (deriv w) u| := by
          apply MeasureTheory.integral_mono (hi.abs) hiabs
          intro u
          dsimp only
          rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have habs : |(-(1 / δ ^ 2))| = 1 / δ ^ 2 := by
    rw [abs_neg, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / δ ^ 2)]
  calc |∫ u : ℝ, w u * Real.cos (δ * u)|
      = (1 / δ ^ 2) * |∫ u : ℝ, deriv (deriv w) u * Real.cos (δ * u)| := by
        rw [integral_mul_cos_eq_second_order hw hc hδ, abs_mul, habs]
    _ ≤ (1 / δ ^ 2) * ∫ u : ℝ, |deriv (deriv w) u| :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (∫ u : ℝ, |deriv (deriv w) u|) / δ ^ 2 := by ring

end OscillatoryKernelDecay
end Zeta23Bridge
