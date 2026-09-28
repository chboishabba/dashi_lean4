import Synthesis.RiemannCompactCosineFourierMassInversion
import Synthesis.RiemannCompactCosineFifthDerivative
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Schwartz rapid decay for compact cosine/sine kernels

A smooth compactly-supported real profile G becomes a complex-valued Schwartz
map after the canonical inclusion ℝ -> ℂ.  Mathlib's Fourier transform
preserves Schwartz space, hence its value decays faster than any polynomial.

The repository angular-frequency cosine and sine transforms are respectively
the real part and minus the imaginary part of that Fourier transform at

  xi = q / (2*pi).

Therefore both transforms inherit arbitrary polynomial decay.  Applying this
to G(u)=P(u)u^k gives rapid decay for every fixed derivative C_P^(k).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real FourierTransform

namespace Synthesis

def complexSchwartzOfCompactSmooth
    (G : ℝ -> ℝ)
    (hGc : HasCompactSupport G)
    (hGs : ContDiff ℝ (⊤ : ℕ∞) G) :
    SchwartzMap ℝ ℂ := by
  have hcomp :
      HasCompactSupport (complexifyRealProfile G) := by
    unfold complexifyRealProfile
    simpa [Function.comp_def] using
      hGc.comp_left
        (g := fun x : ℝ => (x : ℂ))
        (by simp)
  have hsmooth :
      ContDiff ℝ (⊤ : ℕ∞) (complexifyRealProfile G) := by
    unfold complexifyRealProfile
    exact hGs.ofReal
  exact hcomp.toSchwartzMap hsmooth

theorem compactCosineTransform_eq_fourier_re
    {G : ℝ -> ℝ}
    (hG : Continuous G)
    (hGc : HasCompactSupport G)
    (xi : ℝ) :
    compactCosineTransform G (2*Real.pi*xi)
      =
    (FourierTransform.fourier (complexifyRealProfile G) xi).re := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  let F : ℝ -> ℂ := fun u =>
    Complex.exp
      ((-2*Real.pi*u*xi : ℝ) * Complex.I)
      * (G u : ℂ)
  have hGC :
      Integrable (complexifyRealProfile G) :=
    complexifyRealProfile_integrable hG hGc
  have hFmeas : AEStronglyMeasurable F volume := by
    exact (by
      dsimp [F]
      fun_prop : Continuous F).aestronglyMeasurable
  have hF : Integrable F := by
    apply hGC.mono' hFmeas
    exact Filter.Eventually.of_forall fun u => by
      dsimp [F,complexifyRealProfile]
      rw [norm_mul,Complex.norm_exp_ofReal_mul_I]
      simp
  rw [integral_re hF]
  unfold compactCosineTransform
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    dsimp [F]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,sub_zero,Complex.exp_ofReal_mul_I_re]
    rw [show -2*Real.pi*u*xi = -((2*Real.pi*xi)*u) by ring,
      Real.cos_neg]
    ring

theorem compactSineTransform_eq_neg_fourier_im
    {G : ℝ -> ℝ}
    (hG : Continuous G)
    (hGc : HasCompactSupport G)
    (xi : ℝ) :
    compactSineTransform G (2*Real.pi*xi)
      =
    -(FourierTransform.fourier (complexifyRealProfile G) xi).im := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  let F : ℝ -> ℂ := fun u =>
    Complex.exp
      ((-2*Real.pi*u*xi : ℝ) * Complex.I)
      * (G u : ℂ)
  have hGC :
      Integrable (complexifyRealProfile G) :=
    complexifyRealProfile_integrable hG hGc
  have hFmeas : AEStronglyMeasurable F volume := by
    exact (by
      dsimp [F]
      fun_prop : Continuous F).aestronglyMeasurable
  have hF : Integrable F := by
    apply hGC.mono' hFmeas
    exact Filter.Eventually.of_forall fun u => by
      dsimp [F,complexifyRealProfile]
      rw [norm_mul,Complex.norm_exp_ofReal_mul_I]
      simp
  rw [integral_im hF]
  unfold compactSineTransform
  rw [← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    dsimp [F]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      mul_zero,add_zero,Complex.exp_ofReal_mul_I_im]
    rw [show -2*Real.pi*u*xi = -((2*Real.pi*xi)*u) by ring,
      Real.sin_neg]
    ring

theorem compactCosineTransform_abs_le_fourier_norm
    {G : ℝ -> ℝ}
    (hG : Continuous G)
    (hGc : HasCompactSupport G)
    (xi : ℝ) :
    |compactCosineTransform G (2*Real.pi*xi)|
      <=
    ‖FourierTransform.fourier (complexifyRealProfile G) xi‖ := by
  rw [compactCosineTransform_eq_fourier_re hG hGc]
  exact Complex.abs_re_le_norm _

theorem compactSineTransform_abs_le_fourier_norm
    {G : ℝ -> ℝ}
    (hG : Continuous G)
    (hGc : HasCompactSupport G)
    (xi : ℝ) :
    |compactSineTransform G (2*Real.pi*xi)|
      <=
    ‖FourierTransform.fourier (complexifyRealProfile G) xi‖ := by
  rw [compactSineTransform_eq_neg_fourier_im hG hGc,abs_neg]
  exact Complex.abs_im_le_norm _

theorem compactFourierNorm_rapid_decay
    {G : ℝ -> ℝ}
    (hGc : HasCompactSupport G)
    (hGs : ContDiff ℝ (⊤ : ℕ∞) G)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ xi : ℝ,
        |xi|^m
          * ‖FourierTransform.fourier
              (complexifyRealProfile G) xi‖
        <= C := by
  let S : SchwartzMap ℝ ℂ :=
    complexSchwartzOfCompactSmooth G hGc hGs
  let FS : SchwartzMap ℝ ℂ :=
    FourierTransform.fourier S
  obtain ⟨C,hC,hdec⟩ := FS.decay m 0
  refine ⟨C,hC,?_⟩
  intro xi
  have h := hdec xi
  dsimp [FS] at h
  rw [SchwartzMap.fourier_coe] at h
  simpa [S,complexSchwartzOfCompactSmooth,Real.norm_eq_abs] using h

theorem compactCosineTransform_rapid_decay
    {G : ℝ -> ℝ}
    (hGc : HasCompactSupport G)
    (hGs : ContDiff ℝ (⊤ : ℕ∞) G)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ q : ℝ,
        |q|^m * |compactCosineTransform G q| <= C := by
  obtain ⟨C,hC,hdec⟩ :=
    compactFourierNorm_rapid_decay hGc hGs m
  let K : ℝ := (2*Real.pi)^m * C
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K,hK,?_⟩
  intro q
  let xi : ℝ := q/(2*Real.pi)
  have hpi : (2*Real.pi : ℝ) ≠ 0 := by positivity
  have hcos :=
    compactCosineTransform_abs_le_fourier_norm
      hGs.continuous hGc xi
  have hdecxi := hdec xi
  have hq : q = 2*Real.pi*xi := by
    dsimp [xi]
    field_simp [hpi]
  rw [hq] at hcos ⊢
  have hscale :
      |2*Real.pi*xi|^m
        =
      (2*Real.pi)^m * |xi|^m := by
    rw [abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi),mul_pow]
  rw [hscale]
  exact
    (mul_le_mul_of_nonneg_left hcos
      (by positivity : 0 <= (2*Real.pi)^m * |xi|^m)).trans
      (by
        dsimp [K]
        nlinarith [hdecxi])

theorem compactSineTransform_rapid_decay
    {G : ℝ -> ℝ}
    (hGc : HasCompactSupport G)
    (hGs : ContDiff ℝ (⊤ : ℕ∞) G)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ q : ℝ,
        |q|^m * |compactSineTransform G q| <= C := by
  obtain ⟨C,hC,hdec⟩ :=
    compactFourierNorm_rapid_decay hGc hGs m
  let K : ℝ := (2*Real.pi)^m * C
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K,hK,?_⟩
  intro q
  let xi : ℝ := q/(2*Real.pi)
  have hpi : (2*Real.pi : ℝ) ≠ 0 := by positivity
  have hsin :=
    compactSineTransform_abs_le_fourier_norm
      hGs.continuous hGc xi
  have hdecxi := hdec xi
  have hq : q = 2*Real.pi*xi := by
    dsimp [xi]
    field_simp [hpi]
  rw [hq] at hsin ⊢
  have hscale :
      |2*Real.pi*xi|^m
        =
      (2*Real.pi)^m * |xi|^m := by
    rw [abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi),mul_pow]
  rw [hscale]
  exact
    (mul_le_mul_of_nonneg_left hsin
      (by positivity : 0 <= (2*Real.pi)^m * |xi|^m)).trans
      (by
        dsimp [K]
        nlinarith [hdecxi])

theorem compactCosineD1_rapid_decay
    {P : ℝ -> ℝ}
    (hPc : HasCompactSupport P)
    (hPs : ContDiff ℝ (⊤ : ℕ∞) P)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ q : ℝ, |q|^m * |compactCosineD1 P q| <= C := by
  let G : ℝ -> ℝ := fun u => P u * u
  have hGc : HasCompactSupport G := hPc.mul_right
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G := by
    dsimp [G]
    exact hPs.mul contDiff_id
  obtain ⟨C,hC,h⟩ := compactSineTransform_rapid_decay hGc hGs m
  refine ⟨C,hC,?_⟩
  intro q
  unfold compactCosineD1 compactSineTransform
  have heq :
      (∫ u : ℝ, -P u * Real.sin (q*u) * u)
        =
      - ∫ u : ℝ, G u * Real.sin (q*u) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by
      dsimp [G]
      ring
  rw [heq,abs_neg]
  exact h q

theorem compactCosineD2_rapid_decay
    {P : ℝ -> ℝ}
    (hPc : HasCompactSupport P)
    (hPs : ContDiff ℝ (⊤ : ℕ∞) P)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ q : ℝ, |q|^m * |compactCosineD2 P q| <= C := by
  let G : ℝ -> ℝ := fun u => -P u * u^2
  have hGc : HasCompactSupport G := hPc.neg.mul_right
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G := by
    dsimp [G]
    exact hPs.neg.mul (contDiff_id.pow 2)
  simpa [compactCosineD2,compactCosineTransform,G] using
    compactCosineTransform_rapid_decay hGc hGs m

theorem compactCosineD3_rapid_decay
    {P : ℝ -> ℝ}
    (hPc : HasCompactSupport P)
    (hPs : ContDiff ℝ (⊤ : ℕ∞) P)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ q : ℝ, |q|^m * |compactCosineD3 P q| <= C := by
  let G : ℝ -> ℝ := fun u => P u * u^3
  have hGc : HasCompactSupport G := hPc.mul_right
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G := by
    dsimp [G]
    exact hPs.mul (contDiff_id.pow 3)
  obtain ⟨C,hC,h⟩ := compactSineTransform_rapid_decay hGc hGs m
  refine ⟨C,hC,?_⟩
  intro q
  unfold compactCosineD3 compactSineTransform
  simpa [G,mul_assoc] using h q

theorem compactCosineD4_rapid_decay
    {P : ℝ -> ℝ}
    (hPc : HasCompactSupport P)
    (hPs : ContDiff ℝ (⊤ : ℕ∞) P)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ q : ℝ, |q|^m * |compactCosineD4 P q| <= C := by
  let G : ℝ -> ℝ := fun u => P u * u^4
  have hGc : HasCompactSupport G := hPc.mul_right
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G := by
    dsimp [G]
    exact hPs.mul (contDiff_id.pow 4)
  simpa [compactCosineD4,compactCosineTransform,G] using
    compactCosineTransform_rapid_decay hGc hGs m

theorem compactCosineD5_rapid_decay
    {P : ℝ -> ℝ}
    (hPc : HasCompactSupport P)
    (hPs : ContDiff ℝ (⊤ : ℕ∞) P)
    (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ q : ℝ, |q|^m * |compactCosineD5 P q| <= C := by
  let G : ℝ -> ℝ := fun u => -P u * u^5
  have hGc : HasCompactSupport G := hPc.neg.mul_right
  have hGs : ContDiff ℝ (⊤ : ℕ∞) G := by
    dsimp [G]
    exact hPs.neg.mul (contDiff_id.pow 5)
  simpa [compactCosineD5,compactSineTransform,G] using
    compactSineTransform_rapid_decay hGc hGs m

end Synthesis
