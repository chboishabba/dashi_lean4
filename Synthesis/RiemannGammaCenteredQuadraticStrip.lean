import Synthesis.RiemannGammaCenteredQuadraticPointwise

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilOffOrdinateTail
open Zeta23Bridge.LiteralWeilProjectiveStripConstant

def gammaCenteredStripCoeff (g : ℝ → ℝ) (Λ t : ℝ) : ℝ :=
  Real.exp (Λ / 2) *
    (((Λ ^ 2 / 2) * taperMass g)
      + ((Λ ^ 2 / 2) * taperMass (deriv (deriv g))
          + 2 * Λ * taperMass (deriv g)
          + taperMass g)
      + 2 * |t| *
          ((Λ ^ 2 / 2) * taperMass (deriv g)
            + Λ * taperMass g)
      + t ^ 2 * ((Λ ^ 2 / 2) * taperMass g))

theorem taperMass_deriv_gammaCenteredTaper_le {g : ℝ → ℝ} {Λ r : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    (hΛ : 0 ≤ Λ) :
    taperMass (deriv (gammaCenteredTaper g r))
      ≤ r ^ 2 *
        ((Λ ^ 2 / 2) * taperMass (deriv g)
          + Λ * taperMass g) := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_radius hsupp
  have hh : ContDiff ℝ 2 (gammaCenteredTaper g r) :=
    gammaCenteredTaper_contDiff hgs r
  have hhc : HasCompactSupport (gammaCenteredTaper g r) :=
    gammaCenteredTaper_hasCompactSupport hgc r
  have hi1 : Integrable (fun u : ℝ => (Λ ^ 2 / 2) * |deriv g u|) :=
    ((contDiff_one_deriv hgs).continuous.abs.integrable_of_hasCompactSupport
      (hasCompactSupport_of_radius (support_radius_deriv hsupp)).abs).const_mul _
  have hi0 : Integrable (fun u : ℝ => Λ * |g u|) :=
    (hgs.continuous.abs.integrable_of_hasCompactSupport hgc.abs).const_mul _
  have hb : Integrable (fun u : ℝ =>
      r ^ 2 * ((Λ ^ 2 / 2) * |deriv g u| + Λ * |g u|)) :=
    (hi1.add hi0).const_mul _
  have hpt : ∀ u,
      |deriv (gammaCenteredTaper g r) u|
        ≤ r ^ 2 * ((Λ ^ 2 / 2) * |deriv g u| + Λ * |g u|) := by
    intro u
    rw [deriv_gammaCenteredTaper hgs r]
    exact abs_gammaCenteredTaperDeriv_le hsupp hΛ
  have hval :
      (∫ u : ℝ, r ^ 2 *
        ((Λ ^ 2 / 2) * |deriv g u| + Λ * |g u|))
      = r ^ 2 *
        ((Λ ^ 2 / 2) * taperMass (deriv g)
          + Λ * taperMass g) := by
    rw [integral_const_mul, integral_add hi1 hi0,
      integral_const_mul, integral_const_mul]
    rfl
  calc
    taperMass (deriv (gammaCenteredTaper g r))
        ≤ ∫ u : ℝ, r ^ 2 *
          ((Λ ^ 2 / 2) * |deriv g u| + Λ * |g u|) :=
      taperMass_le_of_bound
        (contDiff_one_deriv hh).continuous hhc.deriv hb hpt
    _ = _ := hval

theorem taperMass_deriv2_gammaCenteredTaper_le {g : ℝ → ℝ} {Λ r : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    (hΛ : 0 ≤ Λ) :
    taperMass (deriv (deriv (gammaCenteredTaper g r)))
      ≤ r ^ 2 *
        ((Λ ^ 2 / 2) * taperMass (deriv (deriv g))
          + 2 * Λ * taperMass (deriv g)
          + taperMass g) := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_radius hsupp
  have hh : ContDiff ℝ 2 (gammaCenteredTaper g r) :=
    gammaCenteredTaper_contDiff hgs r
  have hhc : HasCompactSupport (gammaCenteredTaper g r) :=
    gammaCenteredTaper_hasCompactSupport hgc r
  have hi2 : Integrable (fun u : ℝ =>
      (Λ ^ 2 / 2) * |deriv (deriv g) u|) :=
    ((continuous_deriv2 hgs).abs.integrable_of_hasCompactSupport
      (hasCompactSupport_of_radius
        (support_radius_deriv (support_radius_deriv hsupp))).abs).const_mul _
  have hi1 : Integrable (fun u : ℝ => 2 * Λ * |deriv g u|) :=
    ((contDiff_one_deriv hgs).continuous.abs.integrable_of_hasCompactSupport
      (hasCompactSupport_of_radius (support_radius_deriv hsupp)).abs).const_mul _
  have hi0 : Integrable (fun u : ℝ => |g u|) :=
    hgs.continuous.abs.integrable_of_hasCompactSupport hgc.abs
  have hi21 : Integrable (fun u : ℝ =>
      (Λ ^ 2 / 2) * |deriv (deriv g) u|
        + 2 * Λ * |deriv g u|) := hi2.add hi1
  have hb : Integrable (fun u : ℝ =>
      r ^ 2 * ((Λ ^ 2 / 2) * |deriv (deriv g) u|
        + 2 * Λ * |deriv g u| + |g u|)) :=
    (hi21.add hi0).const_mul _
  have hpt : ∀ u,
      |deriv (deriv (gammaCenteredTaper g r)) u|
        ≤ r ^ 2 * ((Λ ^ 2 / 2) * |deriv (deriv g) u|
          + 2 * Λ * |deriv g u| + |g u|) := by
    intro u
    rw [deriv2_gammaCenteredTaper hgs r]
    exact abs_gammaCenteredTaperDeriv2_le hsupp hΛ
  have hval :
      (∫ u : ℝ,
        r ^ 2 * ((Λ ^ 2 / 2) * |deriv (deriv g) u|
          + 2 * Λ * |deriv g u| + |g u|))
      = r ^ 2 *
        ((Λ ^ 2 / 2) * taperMass (deriv (deriv g))
          + 2 * Λ * taperMass (deriv g)
          + taperMass g) := by
    rw [integral_const_mul, integral_add hi21 hi0,
      integral_add hi2 hi1, integral_const_mul, integral_const_mul]
    rfl
  calc
    taperMass (deriv (deriv (gammaCenteredTaper g r)))
        ≤ ∫ u : ℝ,
          r ^ 2 * ((Λ ^ 2 / 2) * |deriv (deriv g) u|
            + 2 * Λ * |deriv g u| + |g u|) :=
      taperMass_le_of_bound
        (continuous_deriv2 hh) hhc.deriv.deriv hb hpt
    _ = _ := hval

theorem stripConst_gammaCentered_le {g : ℝ → ℝ} {Λ : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    (hΛ : 0 ≤ Λ) (t r : ℝ) :
    stripConst (sampleTest (gammaCenteredTaper g r) t 0) Λ
      ≤ r ^ 2 * gammaCenteredStripCoeff g Λ t := by
  let h := gammaCenteredTaper g r
  have hh : ContDiff ℝ 2 h := gammaCenteredTaper_contDiff hgs r
  have hhs : ∀ u, h u ≠ 0 → |u| ≤ Λ := by
    intro u hu
    apply hsupp u
    intro hg
    apply hu
    simp [h, gammaCenteredTaper, hg]
  have hbase := stripConst_sampleTest_le hh hhs t 0
  have h0 := taperMass_gammaCenteredTaper_le hgs hsupp hΛ (r := r)
  have h1 := taperMass_deriv_gammaCenteredTaper_le hgs hsupp hΛ (r := r)
  have h2 := taperMass_deriv2_gammaCenteredTaper_le hgs hsupp hΛ (r := r)
  have habs : |(0 : ℝ) - t| = |t| := by rw [zero_sub, abs_neg]
  have hsq : ((0 : ℝ) - t) ^ 2 = t ^ 2 := by ring
  rw [habs, hsq] at hbase
  have h1' :
      2 * |t| * taperMass (deriv h)
        ≤ 2 * |t| * (r ^ 2 *
          ((Λ ^ 2 / 2) * taperMass (deriv g) + Λ * taperMass g)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h0' :
      t ^ 2 * taperMass h
        ≤ t ^ 2 * (r ^ 2 * ((Λ ^ 2 / 2) * taperMass g)) :=
    mul_le_mul_of_nonneg_left h0 (sq_nonneg t)
  have hinner :
      taperMass h
        + (taperMass (deriv (deriv h))
          + 2 * |t| * taperMass (deriv h)
          + t ^ 2 * taperMass h)
      ≤ r ^ 2 *
        (((Λ ^ 2 / 2) * taperMass g)
          + ((Λ ^ 2 / 2) * taperMass (deriv (deriv g))
              + 2 * Λ * taperMass (deriv g) + taperMass g)
          + 2 * |t| *
              ((Λ ^ 2 / 2) * taperMass (deriv g) + Λ * taperMass g)
          + t ^ 2 * ((Λ ^ 2 / 2) * taperMass g)) := by
    nlinarith
  have hexp : 0 < Real.exp (Λ / 2) := Real.exp_pos _
  have hscaled := mul_le_mul_of_nonneg_left hinner hexp.le
  unfold gammaCenteredStripCoeff
  nlinarith [hbase, hscaled]

end Synthesis
