import Zeta23Bridge.LiteralWeilOddChannelTaper
import Zeta23Bridge.LiteralWeilProjectiveStripConstant
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Quantitative affine bump family

Mathlib's generic ContDiffBump API gives the qualitative support/positivity facts
needed by the historical taper construction, but not derivative-mass bounds in
the radius parameter.

Fix one unit bump once and for all and scale it explicitly:

    psi_{c,R}(u) = psi((u-c)/R),   R>0.

Then the derivative formulas expose all radius dependence:

    psi_{c,R}'  = R^{-1} psi'((u-c)/R),
    psi_{c,R}'' = R^{-2} psi''((u-c)/R).

The support is |u-c|<R.  Subsequent files can use Haar/Lebesgue change of
variables to turn these formulas into exact L1 scaling.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

def unitContDiffBump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def unitBump : ℝ → ℝ := fun x => unitContDiffBump x

theorem unitBump_contDiff : ContDiff ℝ 2 unitBump :=
  unitContDiffBump.contDiff (n := 2)

theorem unitBump_continuous : Continuous unitBump :=
  unitBump_contDiff.continuous

theorem unitBump_hasCompactSupport : HasCompactSupport unitBump :=
  unitContDiffBump.hasCompactSupport

theorem unitBump_nonneg (x : ℝ) : 0 <= unitBump x :=
  unitContDiffBump.nonneg x

theorem unitBump_support {x : ℝ} (hx : unitBump x ≠ 0) :
    |x| < 1 := by
  have hs : x ∈ Function.support unitBump := hx
  change x ∈ Function.support (unitContDiffBump : ℝ → ℝ) at hs
  rw [unitContDiffBump.support_eq] at hs
  have hb := Metric.mem_ball.mp hs
  simpa [Real.dist_eq] using hb

theorem unitBump_at_zero : unitBump 0 = 1 := by
  exact unitContDiffBump.one_of_mem_closedBall
    (Metric.mem_closedBall_self unitContDiffBump.rIn_pos.le)

def scaledUnitBump (c R : ℝ) : ℝ → ℝ :=
  fun u => unitBump ((u - c) / R)

theorem scaledUnitBump_contDiff {R : ℝ} (hR : R ≠ 0) (c : ℝ) :
    ContDiff ℝ 2 (scaledUnitBump c R) := by
  unfold scaledUnitBump
  exact unitBump_contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const hR)

theorem scaledUnitBump_continuous {R : ℝ} (hR : R ≠ 0) (c : ℝ) :
    Continuous (scaledUnitBump c R) :=
  (scaledUnitBump_contDiff hR c).continuous

theorem scaledUnitBump_nonneg (c R u : ℝ) :
    0 <= scaledUnitBump c R u := by
  unfold scaledUnitBump
  exact unitBump_nonneg _

theorem scaledUnitBump_support {c R u : ℝ}
    (hR : 0 < R) (hu : scaledUnitBump c R u ≠ 0) :
    |u - c| < R := by
  have hunit : |(u - c) / R| < 1 := unitBump_support hu
  rw [abs_div, abs_of_pos hR] at hunit
  exact (div_lt_one hR).mp hunit

theorem scaledUnitBump_at_center {c R : ℝ} (hR : R ≠ 0) :
    scaledUnitBump c R c = 1 := by
  unfold scaledUnitBump
  simp [hR, unitBump_at_zero]

def scaledUnitBumpDeriv (c R : ℝ) : ℝ → ℝ :=
  fun u => R⁻¹ * deriv unitBump ((u - c) / R)

def scaledUnitBumpDeriv2 (c R : ℝ) : ℝ → ℝ :=
  fun u => R⁻¹ ^ 2 * deriv (deriv unitBump) ((u - c) / R)

theorem deriv_scaledUnitBump {c R : ℝ} (hR : R ≠ 0) :
    deriv (scaledUnitBump c R) = scaledUnitBumpDeriv c R := by
  funext u
  have hinner :
      HasDerivAt (fun x : ℝ => (x - c) / R) R⁻¹ u := by
    convert ((hasDerivAt_id u).sub_const c).div_const R using 1 <;>
      field_simp [hR]
  have hpsi :
      DifferentiableAt ℝ unitBump ((u - c) / R) :=
    unitBump_contDiff.differentiable (by norm_num) _
  have hcomp := hpsi.hasDerivAt.comp u hinner
  rw [hcomp.deriv]
  unfold scaledUnitBumpDeriv
  ring

theorem deriv2_scaledUnitBump {c R : ℝ} (hR : R ≠ 0) :
    deriv (deriv (scaledUnitBump c R)) = scaledUnitBumpDeriv2 c R := by
  rw [deriv_scaledUnitBump hR]
  funext u
  have hinner :
      HasDerivAt (fun x : ℝ => (x - c) / R) R⁻¹ u := by
    convert ((hasDerivAt_id u).sub_const c).div_const R using 1 <;>
      field_simp [hR]
  have hdpsi :
      DifferentiableAt ℝ (deriv unitBump) ((u - c) / R) := by
    have hcd : ContDiff ℝ 1 (deriv unitBump) :=
      unitBump_contDiff.deriv'
    exact hcd.differentiable (by norm_num) _
  have hcomp :=
    (hdpsi.hasDerivAt.comp u hinner).const_mul R⁻¹
  rw [hcomp.deriv]
  unfold scaledUnitBumpDeriv2
  ring

theorem scaledUnitBump_hasCompactSupport {c R : ℝ} (hR : 0 < R) :
    HasCompactSupport (scaledUnitBump c R) :=
  Zeta23Bridge.LiteralWeilProjectiveStripConstant.hasCompactSupport_of_radius
    (fun u hu => by
      have hs := scaledUnitBump_support hR hu
      have hc : |u| <= |c| + R := by
        calc
          |u| = |(u-c) + c| := by ring_nf
          _ <= |u-c| + |c| := abs_add _ _
          _ <= |c| + R := by linarith
      exact hc)

end Synthesis
