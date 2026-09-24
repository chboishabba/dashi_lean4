import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.Tactic

/-!
# The level-32 eta product and its Fricke transformation

For the CM elliptic curve y² = x³ - x, the classical weight-two level-32
candidate is

  f₃₂(z) = η(4z)^2 η(8z)^2.

Mathlib already proves the exact Dedekind-eta S-transformation.  Applying it
at 8z and 4z gives the concrete Fricke identity

  f₃₂(-1/(32z)) = -32 z² f₃₂(z)

on the upper half-plane.  This is the transformation needed for the Mellin
functional-equation lane.
-/

namespace Synthesis.Millennium.BSD

open Complex
open Set Function
open ModularForm

theorem complex_sqrt_sq_of_ne_zero
    {z : ℂ} (hz : z ≠ 0) :
    Complex.sqrt z ^ 2 = z := by
  rw [Complex.sqrt_eq_exp hz]
  rw [← Complex.exp_nat_mul]
  have harg : (2 : ℂ) * (Complex.log z / 2) = Complex.log z := by ring
  rw [harg, Complex.exp_log hz]

theorem complex_sqrt_I_pow_four :
    Complex.sqrt Complex.I ^ 4 = -1 := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
  rw [complex_sqrt_sq_of_ne_zero Complex.I_ne_zero]
  simp

theorem complex_sqrt_I_inv_pow_four :
    (Complex.sqrt Complex.I)⁻¹ ^ 4 = -1 := by
  rw [inv_pow, complex_sqrt_I_pow_four]
  simp

noncomputable def cmEta32 (z : ℂ) : ℂ :=
  ModularForm.eta (4 * z) ^ 2 * ModularForm.eta (8 * z) ^ 2

theorem cmEta32_differentiableAt
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    DifferentiableAt ℂ cmEta32 z := by
  unfold cmEta32
  apply DifferentiableAt.mul
  · apply DifferentiableAt.pow
    exact (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (by
      simpa [upperHalfPlaneSet] using
        (show 0 < (4 * z).im by
          simp only [mul_im, ofNat_re, ofNat_im, zero_mul, sub_zero]
          exact mul_pos (by norm_num) hz))).comp z (by fun_prop)
  · apply DifferentiableAt.pow
    exact (ModularForm.differentiableAt_eta_of_mem_upperHalfPlaneSet (by
      simpa [upperHalfPlaneSet] using
        (show 0 < (8 * z).im by
          simp only [mul_im, ofNat_re, ofNat_im, zero_mul, sub_zero]
          exact mul_pos (by norm_num) hz))).comp z (by fun_prop)

theorem eta_neg_inv_scaled
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) (m : ℕ) (hm : 0 < m) :
    ModularForm.eta (-1 / ((m : ℂ) * z))
      = (Complex.sqrt Complex.I)⁻¹ *
          (Complex.sqrt ((m : ℂ) * z) *
            ModularForm.eta ((m : ℂ) * z)) := by
  have hmz : ((m : ℂ) * z) ∈ upperHalfPlaneSet := by
    change 0 < (((m : ℂ) * z).im)
    simp only [mul_im, natCast_re, natCast_im, zero_mul, sub_zero]
    exact mul_pos (by exact_mod_cast hm) hz
  have h := ModularForm.eta_comp_eq_csqrt_I_inv hmz
  simpa [Function.comp_apply, Pi.smul_apply] using h

theorem cmEta32_fricke
    {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    cmEta32 (-1 / (32 * z)) = -32 * z ^ 2 * cmEta32 z := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simpa [upperHalfPlaneSet] using hz
  have h4z0 : (4 : ℂ) * z ≠ 0 := mul_ne_zero (by norm_num) hz0
  have h8z0 : (8 : ℂ) * z ≠ 0 := mul_ne_zero (by norm_num) hz0
  have heta8 := eta_neg_inv_scaled hz 8 (by norm_num)
  have heta4 := eta_neg_inv_scaled hz 4 (by norm_num)
  have harg4 : (4 : ℂ) * (-1 / (32 * z)) = -1 / (8 * z) := by
    field_simp
    ring
  have harg8 : (8 : ℂ) * (-1 / (32 * z)) = -1 / (4 * z) := by
    field_simp
    ring
  unfold cmEta32
  rw [harg4, harg8, heta8, heta4]
  rw [mul_pow, mul_pow, mul_pow, mul_pow]
  rw [complex_sqrt_sq_of_ne_zero h8z0,
      complex_sqrt_sq_of_ne_zero h4z0]
  have hc4 := complex_sqrt_I_inv_pow_four
  ring_nf at hc4 ⊢
  rw [← hc4]
  ring

theorem cmEta32_fricke_on_imaginary_axis
    {y : ℝ} (hy : 0 < y) :
    cmEta32 (Complex.I * y⁻¹ / 32)
      = 32 * y ^ 2 * cmEta32 (Complex.I * y) := by
  have hz : (Complex.I * (y : ℂ)) ∈ upperHalfPlaneSet := by
    change 0 < (Complex.I * (y : ℂ)).im
    simp [hy]
  have h := cmEta32_fricke hz
  have htransform :
      -1 / (32 * (Complex.I * (y : ℂ)))
        = Complex.I * (y⁻¹ : ℂ) / 32 := by
    field_simp [ne_of_gt hy]
    ring
  rw [htransform] at h
  convert h using 1 <;> ring

end Synthesis.Millennium.BSD
