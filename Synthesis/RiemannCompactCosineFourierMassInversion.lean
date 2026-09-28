import Synthesis.RiemannCompactCosineFourierMass
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Fourier.Inversion

/-!
# Exact cosine Fourier-mass inversion

For a real even C^2 compactly-supported profile P, the repository cosine
transform

  C_P(q) = ∫ P(u) cos(q*u) du

uses angular frequency q, whereas Mathlib's Fourier transform uses the
character exp(-2*pi*i*u*xi).

This file pays that normalization explicitly.  Evenness kills the sine
channel, giving

  Fourier(P)(xi) = C_P(2*pi*xi).

The L1 compact-cosine theorem supplies integrability of that transform.
Mathlib Fourier inversion at the physical origin then yields

  ∫ C_P(q) dq = 2*pi*P(0).

No distributional Fourier identity is used.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real FourierTransform

namespace Synthesis

def complexifyRealProfile (P : ℝ -> ℝ) : ℝ -> ℂ :=
  fun u => (P u : ℂ)

theorem complexifyRealProfile_integrable
    {P : ℝ -> ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P) :
    Integrable (complexifyRealProfile P) := by
  unfold complexifyRealProfile
  exact (hP.integrable_of_hasCompactSupport hPc).ofReal

theorem integral_mul_sin_eq_zero_of_even
    {P : ℝ -> ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (heven : ∀ u : ℝ, P (-u) = P u)
    (a : ℝ) :
    (∫ u : ℝ, P u * Real.sin (a*u)) = 0 := by
  let f : ℝ -> ℝ := fun u => P u * Real.sin (a*u)
  have hf : Integrable f :=
    (hP.mul (by fun_prop)).integrable_of_hasCompactSupport hPc.mul_right
  have href :=
    MeasureTheory.integral_neg_eq_self f (volume : Measure ℝ)
  have hodd :
      (fun u : ℝ => f (-u)) = fun u => - f u := by
    funext u
    dsimp [f]
    rw [heven u, show a*(-u) = -(a*u) by ring, Real.sin_neg]
    ring
  rw [hodd, integral_neg] at href
  linarith

theorem fourier_complexify_even_eq_cosine
    {P : ℝ -> ℝ}
    (hP : Continuous P)
    (hPc : HasCompactSupport P)
    (heven : ∀ u : ℝ, P (-u) = P u)
    (xi : ℝ) :
    FourierTransform.fourier (complexifyRealProfile P) xi
      =
    (compactCosineTransform P (2*Real.pi*xi) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  let F : ℝ -> ℂ := fun u =>
    Complex.exp
      ((-2*Real.pi*u*xi : ℝ) * Complex.I)
      * (P u : ℂ)
  have hPcomplex :
      Integrable (complexifyRealProfile P) :=
    complexifyRealProfile_integrable hP hPc
  have hFmeas : AEStronglyMeasurable F volume := by
    exact (by
      dsimp [F]
      fun_prop : Continuous F).aestronglyMeasurable
  have hF : Integrable F := by
    apply hPcomplex.mono' hFmeas
    exact Filter.Eventually.of_forall fun u => by
      dsimp [F, complexifyRealProfile]
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I]
      simp
  have hre :
      (∫ u : ℝ, (F u).re)
        =
      compactCosineTransform P (2*Real.pi*xi) := by
    unfold compactCosineTransform
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by
      dsimp [F]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero, Complex.exp_ofReal_mul_I_re]
      rw [show -2*Real.pi*u*xi = -((2*Real.pi*xi)*u) by ring,
        Real.cos_neg]
      ring
  have him :
      (∫ u : ℝ, (F u).im) = 0 := by
    have hs :=
      integral_mul_sin_eq_zero_of_even hP hPc heven (2*Real.pi*xi)
    have heq :
        (fun u : ℝ => (F u).im)
          =
        fun u : ℝ => -(P u * Real.sin ((2*Real.pi*xi)*u)) := by
      funext u
      dsimp [F]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, add_zero, Complex.exp_ofReal_mul_I_im]
      rw [show -2*Real.pi*u*xi = -((2*Real.pi*xi)*u) by ring,
        Real.sin_neg]
      ring
    rw [heq, integral_neg, hs]
    simp
  change (∫ u : ℝ, F u)
      = (compactCosineTransform P (2*Real.pi*xi) : ℂ)
  calc
    (∫ u : ℝ, F u)
      =
    ((∫ u : ℝ, (F u).re : ℝ) : ℂ)
      + ((∫ u : ℝ, (F u).im : ℝ) : ℂ) * Complex.I := by
        exact (integral_re_add_im hF).symm
    _ = (compactCosineTransform P (2*Real.pi*xi) : ℂ) := by
      rw [hre,him]
      simp

theorem compactCosineTransform_integral_eq_two_pi_mul_zero
    {P : ℝ -> ℝ}
    (hP : ContDiff ℝ 2 P)
    (hPc : HasCompactSupport P)
    (heven : ∀ u : ℝ, P (-u) = P u) :
    (∫ q : ℝ, compactCosineTransform P q)
      =
    2 * Real.pi * P 0 := by
  let fC : ℝ -> ℂ := complexifyRealProfile P
  have hPcont : Continuous P := hP.continuous
  have hfC : Integrable fC := by
    dsimp [fC]
    exact complexifyRealProfile_integrable hPcont hPc
  have hFTpoint :
      ∀ xi : ℝ,
        FourierTransform.fourier fC xi
          =
        (compactCosineTransform P (2*Real.pi*xi) : ℂ) := by
    intro xi
    dsimp [fC]
    exact fourier_complexify_even_eq_cosine hPcont hPc heven xi
  have hscaleNe : (2*Real.pi : ℝ) ≠ 0 := by
    positivity
  have hCscaled :
      Integrable
        (fun xi : ℝ =>
          compactCosineTransform P ((2*Real.pi)*xi)) :=
    compactCosineTransform_comp_mul_integrable hP hPc hscaleNe
  have hFTint :
      Integrable (FourierTransform.fourier fC) := by
    have hcplx :
        Integrable
          (fun xi : ℝ =>
            (compactCosineTransform P ((2*Real.pi)*xi) : ℂ)) :=
      hCscaled.ofReal
    exact hcplx.congr
      (Filter.Eventually.of_forall fun xi => by
        symm
        exact hFTpoint xi)
  have hcont0 : ContinuousAt fC 0 := by
    dsimp [fC, complexifyRealProfile]
    exact hPcont.ofReal.continuousAt
  have hinv :=
    MeasureTheory.Integrable.fourierInv_fourier_eq
      hfC hFTint hcont0
  have hinv0 :
      (∫ xi : ℝ, FourierTransform.fourier fC xi)
        = (P 0 : ℂ) := by
    simpa [Real.fourierInv_eq, fC, complexifyRealProfile] using hinv
  have hscaledComplex :
      (∫ xi : ℝ,
        (compactCosineTransform P ((2*Real.pi)*xi) : ℂ))
        =
      (P 0 : ℂ) := by
    calc
      (∫ xi : ℝ,
        (compactCosineTransform P ((2*Real.pi)*xi) : ℂ))
        =
      (∫ xi : ℝ, FourierTransform.fourier fC xi) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun xi => (hFTpoint xi).symm
      _ = (P 0 : ℂ) := hinv0
  have hscaledReal :
      (∫ xi : ℝ,
        compactCosineTransform P ((2*Real.pi)*xi))
        =
      P 0 := by
    have hcast :
        ((∫ xi : ℝ,
          compactCosineTransform P ((2*Real.pi)*xi) : ℝ) : ℂ)
          =
        (∫ xi : ℝ,
          (compactCosineTransform P ((2*Real.pi)*xi) : ℂ)) := by
      symm
      exact integral_complex_ofReal
    apply Complex.ofReal_injective
    rw [hcast]
    exact hscaledComplex
  have hchange :=
    Measure.integral_comp_mul_left
      (compactCosineTransform P) (2*Real.pi)
  have habs :
      |(2*Real.pi : ℝ)⁻¹|
        = 1/(2*Real.pi) := by
    rw [abs_of_pos (inv_pos.mpr (by positivity))]
    rfl
  have hchange' :
      (∫ xi : ℝ,
        compactCosineTransform P ((2*Real.pi)*xi))
        =
      (1/(2*Real.pi))
        * (∫ q : ℝ, compactCosineTransform P q) := by
    simpa [habs, smul_eq_mul] using hchange
  rw [hchange'] at hscaledReal
  have hp : 0 < Real.pi := Real.pi_pos
  field_simp [ne_of_gt hp] at hscaledReal ⊢
  nlinarith

end Synthesis
