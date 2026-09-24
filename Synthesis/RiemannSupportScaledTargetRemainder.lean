import Synthesis.RiemannArbitraryRadiusTargetRemainder
import Zeta23Bridge.LiteralWeilProjectiveStripConstant

/-!
# Support-scaled moment bounds for the arbitrary-radius remainder

For a compactly supported taper with |u| <= Lambda,

  Q0(a) <= cosh(|a| Lambda) M,
  Q2(a) <= Lambda^2 cosh(|a| Lambda) M,
  Q4(a) <= Lambda^4 cosh(|a| Lambda) M,

where M = integral |g|.

Consequently the exact arbitrary-radius remainder depends on r and Lambda only
through the expected dimensionless combinations r^2 Lambda^4 and
r^4 Lambda^6, up to the taper mass and horizontal cosh factor.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilTargetDefectLeadingCoefficient
open Zeta23Bridge.LiteralWeilProjectiveStripConstant

theorem cosh_mul_le_support_cosh
    {a u Lambda : ℝ}
    (hLambda : 0 <= Lambda)
    (hu : |u| <= Lambda) :
    Real.cosh (a * u)
      <= Real.cosh (|a| * Lambda) := by
  apply Real.cosh_le_cosh.mpr
  rw [abs_mul]
  have hmul :
      |a| * |u| <= |a| * Lambda :=
    mul_le_mul_of_nonneg_left hu (abs_nonneg a)
  simpa [abs_of_nonneg (mul_nonneg (abs_nonneg a) hLambda)] using hmul

theorem absMom0_le_support
    {g : ℝ → ℝ} {a Lambda : ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hLambda : 0 <= Lambda)
    (hsupp : ∀ u, g u ≠ 0 -> |u| <= Lambda) :
    absMom0 g a
      <= Real.cosh (|a| * Lambda) * taperMass g := by
  have hleft :
      Integrable
        (fun u : ℝ => |g u| * Real.cosh (a * u)) :=
    taper_integrable hg.abs hgc.abs (by fun_prop)
  have hright :
      Integrable
        (fun u : ℝ => Real.cosh (|a| * Lambda) * |g u|) :=
    (hg.abs.integrable_of_hasCompactSupport hgc.abs).const_mul _
  unfold absMom0 taperMass
  calc
    (∫ u : ℝ, |g u| * Real.cosh (a * u))
      <=
      ∫ u : ℝ, Real.cosh (|a| * Lambda) * |g u| := by
        exact integral_mono hleft hright (fun u => by
          by_cases hgu : g u = 0
          · simp [hgu]
          · have hc := cosh_mul_le_support_cosh
              hLambda (hsupp u hgu)
            have hg0 : 0 <= |g u| := abs_nonneg _
            nlinarith)
    _ = Real.cosh (|a| * Lambda) * ∫ u : ℝ, |g u| := by
      rw [integral_const_mul]

theorem absMom2_le_support
    {g : ℝ → ℝ} {a Lambda : ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hLambda : 0 <= Lambda)
    (hsupp : ∀ u, g u ≠ 0 -> |u| <= Lambda) :
    absMom2 g a
      <= Lambda ^ 2 * Real.cosh (|a| * Lambda) * taperMass g := by
  have hleft :
      Integrable
        (fun u : ℝ => |g u| * (u ^ 2 * Real.cosh (a * u))) :=
    taper_integrable hg.abs hgc.abs (by fun_prop)
  have hbase :
      Integrable (fun u : ℝ => |g u|) :=
    hg.abs.integrable_of_hasCompactSupport hgc.abs
  unfold absMom2 taperMass
  calc
    (∫ u : ℝ, |g u| * (u ^ 2 * Real.cosh (a * u)))
      <=
      ∫ u : ℝ,
        (Lambda ^ 2 * Real.cosh (|a| * Lambda)) * |g u| := by
        exact integral_mono hleft (hbase.const_mul _) (fun u => by
          by_cases hgu : g u = 0
          · simp [hgu]
          · have hu := hsupp u hgu
            have hu2 : u ^ 2 <= Lambda ^ 2 := by
              nlinarith [sq_abs u]
            have hc := cosh_mul_le_support_cosh hLambda hu
            have hcosh0 : 0 <= Real.cosh (a*u) :=
              (Real.cosh_pos _).le
            have hLcosh0 :
                0 <= Real.cosh (|a|*Lambda) :=
              (Real.cosh_pos _).le
            have hg0 : 0 <= |g u| := abs_nonneg _
            have hprod :
                u^2 * Real.cosh (a*u)
                  <= Lambda^2 * Real.cosh (|a|*Lambda) :=
              mul_le_mul hu2 hc hcosh0 (sq_nonneg Lambda)
            nlinarith)
    _ =
      Lambda ^ 2 * Real.cosh (|a| * Lambda)
        * ∫ u : ℝ, |g u| := by
      rw [integral_const_mul]

theorem absMom4_le_support
    {g : ℝ → ℝ} {a Lambda : ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hLambda : 0 <= Lambda)
    (hsupp : ∀ u, g u ≠ 0 -> |u| <= Lambda) :
    absMom4 g a
      <= Lambda ^ 4 * Real.cosh (|a| * Lambda) * taperMass g := by
  have hleft :
      Integrable
        (fun u : ℝ => |g u| * (u ^ 4 * Real.cosh (a * u))) :=
    taper_integrable hg.abs hgc.abs (by fun_prop)
  have hbase :
      Integrable (fun u : ℝ => |g u|) :=
    hg.abs.integrable_of_hasCompactSupport hgc.abs
  unfold absMom4 taperMass
  calc
    (∫ u : ℝ, |g u| * (u ^ 4 * Real.cosh (a * u)))
      <=
      ∫ u : ℝ,
        (Lambda ^ 4 * Real.cosh (|a| * Lambda)) * |g u| := by
        exact integral_mono hleft (hbase.const_mul _) (fun u => by
          by_cases hgu : g u = 0
          · simp [hgu]
          · have hu := hsupp u hgu
            have hu2 : u ^ 2 <= Lambda ^ 2 := by
              nlinarith [sq_abs u]
            have hu4 : u ^ 4 <= Lambda ^ 4 := by
              nlinarith [sq_nonneg (u^2), sq_nonneg (Lambda^2)]
            have hc := cosh_mul_le_support_cosh hLambda hu
            have hcosh0 : 0 <= Real.cosh (a*u) :=
              (Real.cosh_pos _).le
            have hg0 : 0 <= |g u| := abs_nonneg _
            have hprod :
                u^4 * Real.cosh (a*u)
                  <= Lambda^4 * Real.cosh (|a|*Lambda) :=
              mul_le_mul hu4 hc hcosh0 (by positivity)
            nlinarith)
    _ =
      Lambda ^ 4 * Real.cosh (|a| * Lambda)
        * ∫ u : ℝ, |g u| := by
      rw [integral_const_mul]

theorem defectRemainder4_le_support
    {g : ℝ → ℝ} {a Lambda : ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hLambda : 0 <= Lambda)
    (hsupp : ∀ u, g u ≠ 0 -> |u| <= Lambda) :
    defectRemainder4 g a
      <=
    (17 / 12 : ℝ) * Lambda ^ 4
      * Real.cosh (|a| * Lambda)
      * taperMass g ^ 2 := by
  have q4a := absMom4_le_support hg hgc hLambda hsupp (a := a)
  have q0a := absMom0_le_support hg hgc hLambda hsupp (a := a)
  have q40 := absMom4_le_support hg hgc hLambda hsupp (a := (0:ℝ))
  have q00 := absMom0_le_support hg hgc hLambda hsupp (a := (0:ℝ))
  have hM : 0 <= taperMass g := taperMass_nonneg g
  have hC : 1 <= Real.cosh (|a| * Lambda) := Real.one_le_cosh _
  have hL : 0 <= Lambda ^ 4 := by positivity
  simp only [abs_zero, zero_mul, Real.cosh_zero, one_mul] at q40 q00
  unfold defectRemainder4
  nlinarith [mul_nonneg hL hM]

theorem defectRemainder6_le_support
    {g : ℝ → ℝ} {a Lambda : ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (hLambda : 0 <= Lambda)
    (hsupp : ∀ u, g u ≠ 0 -> |u| <= Lambda) :
    defectRemainder6 g a
      <=
    (5 / 12 : ℝ) * Lambda ^ 6
      * Real.cosh (|a| * Lambda)
      * taperMass g ^ 2 := by
  have q2a := absMom2_le_support hg hgc hLambda hsupp (a := a)
  have q40 := absMom4_le_support hg hgc hLambda hsupp (a := (0:ℝ))
  have hM : 0 <= taperMass g := taperMass_nonneg g
  have hL2 : 0 <= Lambda ^ 2 := by positivity
  have hL4 : 0 <= Lambda ^ 4 := by positivity
  simp only [abs_zero, zero_mul, Real.cosh_zero, one_mul] at q40
  unfold defectRemainder6
  nlinarith [mul_nonneg hL2 hL4, mul_nonneg hM hM]

end Synthesis
