import Synthesis.RiemannQuantitativeScaledBump

/-!
# Exact L1 scaling of the quantitative affine bump

For R>0 and psi_{c,R}(u)=psi((u-c)/R),

    ||psi_{c,R}||_1    = R ||psi||_1,
    ||psi_{c,R}'||_1   = ||psi'||_1,
    ||psi_{c,R}''||_1  = R^{-1} ||psi''||_1.

Translation does not affect Lebesgue integrals; scaling follows from Haar
invariance on the real line.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilProjectiveStripConstant

def unitBumpMass0 : ℝ := taperMass unitBump
def unitBumpMass1 : ℝ := taperMass (deriv unitBump)
def unitBumpMass2 : ℝ := taperMass (deriv (deriv unitBump))

theorem unitBumpMass0_nonneg : 0 <= unitBumpMass0 :=
  taperMass_nonneg _
theorem unitBumpMass1_nonneg : 0 <= unitBumpMass1 :=
  taperMass_nonneg _
theorem unitBumpMass2_nonneg : 0 <= unitBumpMass2 :=
  taperMass_nonneg _

theorem integral_abs_affine_scale
    (f : ℝ → ℝ) {c R : ℝ} (hR : 0 < R) :
    (∫ u : ℝ, |f ((u - c) / R)|)
      = R * ∫ x : ℝ, |f x| := by
  let F : ℝ → ℝ := fun x => |f (x / R)|
  have htrans :
      (∫ u : ℝ, F (u + (-c))) = ∫ u : ℝ, F u :=
    integral_add_right_eq_self F (-c)
  have hrewrite :
      (fun u : ℝ => |f ((u - c) / R)|)
        = fun u => F (u + (-c)) := by
    funext u
    dsimp [F]
    congr 2 <;> ring
  rw [hrewrite, htrans]
  dsimp [F]
  have hscale :=
    Measure.integral_comp_mul_left
      (fun x : ℝ => |f x|) R⁻¹
  have hRne : R ≠ 0 := ne_of_gt hR
  have habs : |(R⁻¹)⁻¹| = R := by
    rw [inv_inv, abs_of_pos hR]
  simpa [div_eq_inv_mul, habs, smul_eq_mul] using hscale

theorem taperMass_scaledUnitBump
    {c R : ℝ} (hR : 0 < R) :
    taperMass (scaledUnitBump c R) = R * unitBumpMass0 := by
  unfold taperMass scaledUnitBump unitBumpMass0
  exact integral_abs_affine_scale unitBump hR

theorem taperMass_deriv_scaledUnitBump
    {c R : ℝ} (hR : 0 < R) :
    taperMass (deriv (scaledUnitBump c R)) = unitBumpMass1 := by
  have hRne : R ≠ 0 := ne_of_gt hR
  rw [deriv_scaledUnitBump hRne]
  unfold taperMass scaledUnitBumpDeriv unitBumpMass1
  have hscale :=
    integral_abs_affine_scale (deriv unitBump) (c := c) hR
  have hRinv : |R⁻¹| = R⁻¹ := abs_of_pos (inv_pos.mpr hR)
  have hconst :
      (∫ u : ℝ, |R⁻¹ * deriv unitBump ((u - c) / R)|)
        = R⁻¹ *
          ∫ u : ℝ, |deriv unitBump ((u - c) / R)| := by
    simp_rw [abs_mul, hRinv]
    rw [integral_const_mul]
  rw [hconst, hscale]
  field_simp [ne_of_gt hR]

theorem taperMass_deriv2_scaledUnitBump
    {c R : ℝ} (hR : 0 < R) :
    taperMass (deriv (deriv (scaledUnitBump c R)))
      = R⁻¹ * unitBumpMass2 := by
  have hRne : R ≠ 0 := ne_of_gt hR
  rw [deriv2_scaledUnitBump hRne]
  unfold taperMass scaledUnitBumpDeriv2 unitBumpMass2
  have hscale :=
    integral_abs_affine_scale (deriv (deriv unitBump)) (c := c) hR
  have hRinv2 : |R⁻¹ ^ 2| = R⁻¹ ^ 2 := by
    rw [abs_pow, abs_of_pos (inv_pos.mpr hR)]
  have hconst :
      (∫ u : ℝ, |R⁻¹ ^ 2 * deriv (deriv unitBump) ((u - c) / R)|)
        = R⁻¹ ^ 2 *
          ∫ u : ℝ, |deriv (deriv unitBump) ((u - c) / R)| := by
    simp_rw [abs_mul, hRinv2]
    rw [integral_const_mul]
  rw [hconst, hscale]
  field_simp [ne_of_gt hR]
  ring

end Synthesis
