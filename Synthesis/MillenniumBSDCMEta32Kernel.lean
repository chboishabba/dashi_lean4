import Synthesis.MillenniumBSDCMEta32Fricke
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.Tactic

/-!
# Level-normalized CM eta kernel

Normalize the imaginary-axis eta product by the square root of the conductor:

  F(x) = f32(i x / sqrt(32)).

The Fricke relation then becomes the exact self-dual Mellin symmetry

  F(1/x) = x^2 F(x)

for x>0.  Thus the eventual FE-pair has weight 2 and root number +1, with
no residual level factor.
-/

namespace Synthesis.Millennium.BSD

open Complex
open Set

noncomputable def cmEta32Scale : ℝ := Real.sqrt 32

theorem cmEta32Scale_pos : 0 < cmEta32Scale := by
  unfold cmEta32Scale
  positivity

theorem cmEta32Scale_ne_zero : cmEta32Scale ≠ 0 :=
  ne_of_gt cmEta32Scale_pos

theorem cmEta32Scale_sq : cmEta32Scale ^ 2 = 32 := by
  unfold cmEta32Scale
  rw [sq_sqrt]
  norm_num

noncomputable def cmEta32Kernel (x : ℝ) : ℂ :=
  cmEta32 (Complex.I * ((x / cmEta32Scale : ℝ) : ℂ))

theorem cmEta32Kernel_arg_mem_upperHalfPlane
    {x : ℝ} (hx : 0 < x) :
    Complex.I * ((x / cmEta32Scale : ℝ) : ℂ) ∈ upperHalfPlaneSet := by
  change 0 < (Complex.I * ((x / cmEta32Scale : ℝ) : ℂ)).im
  simp [div_pos hx cmEta32Scale_pos]

theorem cmEta32_fricke_normalized_argument
    {x : ℝ} (hx : 0 < x) :
    -1 / (32 *
      (Complex.I * ((x / cmEta32Scale : ℝ) : ℂ)))
      = Complex.I * (((1 / x) / cmEta32Scale : ℝ) : ℂ) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hs0 : cmEta32Scale ≠ 0 := cmEta32Scale_ne_zero
  have hs2 := cmEta32Scale_sq
  field_simp [hx0, hs0]
  push_cast at hs2 ⊢
  ring_nf at hs2 ⊢
  nlinarith

theorem cmEta32_fricke_normalized_multiplier
    {x : ℝ} :
    -32 *
        (Complex.I * ((x / cmEta32Scale : ℝ) : ℂ)) ^ 2
      = (x ^ 2 : ℝ) := by
  have hs2 := cmEta32Scale_sq
  have hs0 : cmEta32Scale ≠ 0 := cmEta32Scale_ne_zero
  field_simp [hs0]
  push_cast at hs2 ⊢
  ring_nf at hs2 ⊢
  nlinarith

theorem cmEta32Kernel_inversion
    {x : ℝ} (hx : 0 < x) :
    cmEta32Kernel (1 / x) =
      (x ^ 2 : ℂ) * cmEta32Kernel x := by
  unfold cmEta32Kernel
  have h := cmEta32_fricke (cmEta32Kernel_arg_mem_upperHalfPlane hx)
  rw [cmEta32_fricke_normalized_argument hx] at h
  rw [cmEta32_fricke_normalized_multiplier] at h
  exact h

theorem cmEta32Kernel_inversion_rpow
    {x : ℝ} (hx : 0 < x) :
    cmEta32Kernel (1 / x) =
      ((x ^ (2 : ℝ) : ℝ) : ℂ) * cmEta32Kernel x := by
  rw [show x ^ (2 : ℝ) = x ^ (2 : ℕ) by
    exact (Real.rpow_natCast x 2).symm]
  exact cmEta32Kernel_inversion hx

end Synthesis.Millennium.BSD
