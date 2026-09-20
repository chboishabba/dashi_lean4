import Zeta23Bridge.OscillatoryKernelDecay
import Zeta23Bridge.LiteralWeilParityBalance
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Cosine-transform inversion at zero

For an even compactly supported C^2 real function h, the repo cosine transform

    cosFT h y = integral_u h(u) cos(yu)

is integrable and satisfies

    integral_y cosFT h y = 2*pi*h(0).

This is the exact normalization needed to kill the constant part of the digamma
series for centered tapers h with h(0)=0.
-/

noncomputable section

open MeasureTheory Set Filter Complex
open scoped Real FourierTransform RealInnerProductSpace Complex

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.OscillatoryKernelDecay

def realAsComplex (h : ℝ → ℝ) : ℝ → ℂ :=
  fun x => (h x : ℂ)

theorem realAsComplex_integrable {h : ℝ → ℝ}
    (hh : Continuous h) (hcompact : HasCompactSupport h) :
    Integrable (realAsComplex h) := by
  exact (hh.integrable_of_hasCompactSupport hcompact).ofReal

theorem fourier_realAsComplex_eq_cosFT {h : ℝ → ℝ}
    (hh : Continuous h) (hcompact : HasCompactSupport h)
    (heven : ∀ x, h (-x) = h x) (w : ℝ) :
    𝓕 (realAsComplex h) w
      = ((cosFT h (2*Real.pi*w) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hint :
      Integrable
        (fun x : ℝ =>
          Complex.exp (↑(-2*Real.pi*x*w) * Complex.I)
            • realAsComplex h x) :=
    (Real.fourierIntegral_convergent_iff w).2
      (realAsComplex_integrable hh hcompact)
  apply Complex.ext
  · rw [← integral_re hint]
    simp only [realAsComplex, Complex.exp_mul_I, Complex.real_smul,
      Complex.ofReal_re, Complex.ofReal_im, mul_re, mul_zero, sub_zero]
    unfold cosFT
    congr 1
    funext x
    rw [Real.cos_neg]
    ring
  · rw [← integral_im hint]
    simp only [realAsComplex, Complex.exp_mul_I, Complex.imag_smul,
      Complex.ofReal_re, Complex.ofReal_im, mul_im, zero_mul, add_zero]
    let f : ℝ → ℝ :=
      fun x => h x * Real.sin (2*Real.pi*x*w)
    have hf : Integrable f := by
      apply Integrable.mono'
        (hh.abs.integrable_of_hasCompactSupport hcompact.abs)
      · fun_prop
      · filter_upwards with x
        unfold f
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg (h x))
          (Real.abs_sin_le_one _)
    have hodd : (fun x : ℝ => f (-x)) = fun x => -f x := by
      funext x
      unfold f
      rw [heven, show 2*Real.pi*(-x)*w = -(2*Real.pi*x*w) by ring,
        Real.sin_neg]
      ring
    have hinv :
        (∫ x : ℝ, f (-x)) = ∫ x : ℝ, f x := by
      simpa using
        (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
          (Homeomorph.neg ℝ).measurableEmbedding f
    rw [hodd, integral_neg] at hinv
    have hz : (∫ x : ℝ, f x) = 0 := by linarith
    simpa [f, mul_comm, mul_left_comm, mul_assoc] using hz

theorem cosFT_integrable {h : ℝ → ℝ}
    (hC2 : ContDiff ℝ 2 h) (hcompact : HasCompactSupport h) :
    Integrable (cosFT h) := by
  have hcont : Continuous (cosFT h) := by
    unfold cosFT
    fun_prop
  have hlocal :
      IntegrableOn (cosFT h) (Set.Icc (-1) 1) :=
    hcont.integrableOn_Icc
  have hD2 :
      Integrable (fun u : ℝ => |deriv (deriv h) u|) :=
    (hC2.deriv'.continuous_deriv le_rfl).abs.integrable_of_hasCompactSupport
      hcompact.deriv.deriv.abs
  let C : ℝ := ∫ u : ℝ, |deriv (deriv h) u|
  have hC0 : 0 <= C := integral_nonneg fun _ => abs_nonneg _
  have htail :
      ∀ y : ℝ, 1 <= |y| -> |cosFT h y| <= C / y^2 := by
    intro y hy
    have hy0 : y ≠ 0 := by
      intro hz
      simp [hz] at hy
    unfold cosFT
    exact abs_integral_mul_cos_le hC2 hcompact hy0
  have hmajor :
      IntegrableOn (fun y : ℝ => C / y^2)
        ((Set.Icc (-1) 1)ᶜ) := by
    have hp :
        IntegrableOn (fun y : ℝ => C * |y|⁻¹^2)
          ((Set.Icc (-1) 1)ᶜ) := by
      exact (integrableOn_compl_Icc_rpow_neg (by norm_num : (1:ℝ) < 2)
        (by norm_num : (0:ℝ) < 1)).const_mul C
    apply hp.congr
    filter_upwards [ae_restrict_mem measurableSet_compl] with y hy
    have hyabs : 1 <= |y| := by
      simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hy
      rcases hy with hy | hy
      · have : |y| > 1 := by
          rw [abs_of_neg (lt_trans hy (by norm_num))]
          linarith
        linarith
      · have : |y| > 1 := by
          rw [abs_of_pos (lt_trans (by norm_num) hy)]
          exact hy
        linarith
    field_simp
    rw [sq_abs]
  have htailInt :
      IntegrableOn (cosFT h) ((Set.Icc (-1) 1)ᶜ) := by
    apply Integrable.mono' hmajor
    · exact hcont.aestronglyMeasurable.restrict
    · filter_upwards [ae_restrict_mem measurableSet_compl] with y hy
      have hyabs : 1 <= |y| := by
        simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hy
        rcases hy with hy | hy
        · rw [abs_of_neg (lt_trans hy (by norm_num))]
          linarith
        · rw [abs_of_pos (lt_trans (by norm_num) hy)]
          linarith
      exact htail y hyabs
  exact integrableOn_union hlocal htailInt
    (by simp [Set.union_compl_self])

theorem integral_cosFT_eq_two_pi_mul_value_zero {h : ℝ → ℝ}
    (hC2 : ContDiff ℝ 2 h) (hcompact : HasCompactSupport h)
    (heven : ∀ x, h (-x)=h x) :
    (∫ y : ℝ, cosFT h y) = 2*Real.pi*h 0 := by
  have hf := realAsComplex_integrable hC2.continuous hcompact
  have hCos := cosFT_integrable hC2 hcompact
  have hFint : Integrable (𝓕 (realAsComplex h)) := by
    have hscaled :
        Integrable
          (fun w : ℝ => ((cosFT h (2*Real.pi*w) : ℝ) : ℂ)) := by
      have hpi : 0 < 2*Real.pi := mul_pos (by norm_num) Real.pi_pos
      have hcomp :
          Integrable (fun w : ℝ => cosFT h ((2*Real.pi)*w)) := by
        rw [← integrable_comp_mul_left_iff (ne_of_gt hpi)]
        exact hCos
      exact hcomp.ofReal
    apply hscaled.congr
    filter_upwards with w
    exact (fourier_realAsComplex_eq_cosFT
      hC2.continuous hcompact heven w).symm
  have hinv :=
    hf.fourierInv_fourier_eq hFint
      (hC2.continuous.ofReal).continuousAt
  have hinv0 := hinv (v:=0)
  rw [Real.fourierInv_eq'] at hinv0
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul, realAsComplex] at hinv0
  have hchange := Measure.integral_comp_mul_left
    (fun y : ℝ => ((cosFT h y : ℝ) : ℂ)) (2*Real.pi)
  have hpi : 0 < 2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  rw [abs_of_pos (inv_pos.mpr hpi)] at hchange
  have hFpoint :
      ∀ w, 𝓕 (realAsComplex h) w
        = ((cosFT h (2*Real.pi*w) : ℝ) : ℂ) :=
    fun w => fourier_realAsComplex_eq_cosFT
      hC2.continuous hcompact heven w
  simp_rw [hFpoint] at hinv0
  rw [hchange] at hinv0
  have hre := congrArg Complex.re hinv0
  push_cast at hre
  field_simp [ne_of_gt hpi] at hre
  nlinarith [Real.pi_pos]

theorem integral_cosFT_centered_eq_zero {h : ℝ → ℝ}
    (hC2 : ContDiff ℝ 2 h) (hcompact : HasCompactSupport h)
    (heven : ∀ x, h (-x)=h x) (h0 : h 0 = 0) :
    (∫ y : ℝ, cosFT h y) = 0 := by
  rw [integral_cosFT_eq_two_pi_mul_value_zero hC2 hcompact heven,
    h0, mul_zero]

end Synthesis
