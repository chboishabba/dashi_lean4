import Synthesis.RiemannGammaCenteredQuadraticStrip
import Zeta23Bridge.ReflectionPairCurvatureBound

/-!
# Explicit curvature of the centered taper

For h_r(u)=g(u)(cos(r u)-1), combine the centered L1 derivative estimates with
the literal reflection-pair curvature theorem.

Uniformly for every critical-strip horizontal height |a| <= 1/2,

  pairWeightCurvature h_r a
    <= 4 cosh(Lambda/2) r^2 *
       [ (Lambda^2/2) M2
         + (2 Lambda + Lambda^2/2) M1
         + (1 + Lambda + Lambda^2/2) M0 ],

where Mk is the L1 mass of the kth derivative of g.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilProjectiveStripConstant
open Zeta23Bridge.ReflectionPairKernelDecay
open Zeta23Bridge.ReflectionPairCurvatureBound

def centeredPairCurvatureCoeff (g : ℝ → ℝ) (Lambda r : ℝ) : ℝ :=
  4 * Real.cosh (Lambda / 2) * r ^ 2 *
    ((Lambda ^ 2 / 2) * taperMass (deriv (deriv g))
      + (2 * Lambda + Lambda ^ 2 / 2) * taperMass (deriv g)
      + (1 + Lambda + Lambda ^ 2 / 2) * taperMass g)

theorem centeredPairCurvatureCoeff_nonneg
    (g : ℝ → ℝ) {Lambda : ℝ} (hLambda : 0 <= Lambda) (r : ℝ) :
    0 <= centeredPairCurvatureCoeff g Lambda r := by
  have h0 := taperMass_nonneg g
  have h1 := taperMass_nonneg (deriv g)
  have h2 := taperMass_nonneg (deriv (deriv g))
  unfold centeredPairCurvatureCoeff
  positivity

theorem tsupport_gammaCenteredTaper_subset_closedBall
    {g : ℝ → ℝ} {Lambda r : ℝ}
    (hsupp : ∀ u, g u ≠ 0 → |u| <= Lambda) :
    tsupport (gammaCenteredTaper g r) ⊆ Metric.closedBall (0 : ℝ) Lambda := by
  have hsupport :
      Function.support (gammaCenteredTaper g r)
        ⊆ {u : ℝ | |u| <= Lambda} := by
    intro u hu
    apply hsupp u
    intro hgu
    apply hu
    simp [gammaCenteredTaper, hgu]
  have hclosed : IsClosed {u : ℝ | |u| <= Lambda} :=
    isClosed_le continuous_abs continuous_const
  have hts :
      tsupport (gammaCenteredTaper g r)
        ⊆ {u : ℝ | |u| <= Lambda} :=
    closure_minimal hsupport hclosed
  intro u hu
  have habs := hts hu
  simp only [Metric.mem_closedBall, Real.dist_eq, sub_zero]
  exact habs

theorem pairWeightCurvature_gammaCenteredTaper_le
    {g : ℝ → ℝ} {Lambda r a : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hsupp : ∀ u, g u ≠ 0 → |u| <= Lambda)
    (hLambda : 0 <= Lambda)
    (ha : |a| <= 1 / 2) :
    pairWeightCurvature (gammaCenteredTaper g r) a
      <= centeredPairCurvatureCoeff g Lambda r := by
  let h := gammaCenteredTaper g r
  have hh : ContDiff ℝ 2 h := gammaCenteredTaper_contDiff hgs r
  have hhc : HasCompactSupport h :=
    gammaCenteredTaper_hasCompactSupport (hasCompactSupport_of_radius hsupp) r
  have hsub :
      tsupport h ⊆ Metric.closedBall (0 : ℝ) Lambda :=
    tsupport_gammaCenteredTaper_subset_closedBall hsupp
  have hcurv :=
    pairWeightCurvature_le hh hhc hLambda hsub ha

  have h0 := taperMass_gammaCenteredTaper_le hgs hsupp hLambda (r := r)
  have h1 := taperMass_deriv_gammaCenteredTaper_le hgs hsupp hLambda (r := r)
  have h2 := taperMass_deriv2_gammaCenteredTaper_le hgs hsupp hLambda (r := r)

  have hi0 : Integrable (fun u : ℝ => |h u|) :=
    hh.continuous.abs.integrable_of_hasCompactSupport hhc.abs
  have hi1 : Integrable (fun u : ℝ => |deriv h u|) :=
    (contDiff_one_deriv hh).continuous.abs.integrable_of_hasCompactSupport
      hhc.deriv.abs
  have hi2 : Integrable (fun u : ℝ => |deriv (deriv h) u|) :=
    (continuous_deriv2 hh).abs.integrable_of_hasCompactSupport
      hhc.deriv.deriv.abs
  have hi21 : Integrable
      (fun u : ℝ => |deriv (deriv h) u| + |deriv h u|) :=
    hi2.add hi1

  have hcurv' :
      pairWeightCurvature h a
        <= 4 * Real.cosh (Lambda / 2) *
          (taperMass (deriv (deriv h))
            + taperMass (deriv h) + taperMass h) := by
    calc
      pairWeightCurvature h a
          <= ∫ u : ℝ,
            4 * Real.cosh (Lambda / 2) *
              (|deriv (deriv h) u| + |deriv h u| + |h u|) := hcurv
      _ = 4 * Real.cosh (Lambda / 2) *
          (taperMass (deriv (deriv h))
            + taperMass (deriv h) + taperMass h) := by
        rw [integral_const_mul, integral_add hi21 hi0,
          integral_add hi2 hi1]

  have hfac : 0 <= 4 * Real.cosh (Lambda / 2) := by
    positivity
  have hmass :
      taperMass (deriv (deriv h))
          + taperMass (deriv h) + taperMass h
      <= r ^ 2 *
        ((Lambda ^ 2 / 2) * taperMass (deriv (deriv g))
          + (2 * Lambda + Lambda ^ 2 / 2) * taperMass (deriv g)
          + (1 + Lambda + Lambda ^ 2 / 2) * taperMass g) := by
    dsimp [h] at h0 h1 h2 ⊢
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hmass hfac
  unfold centeredPairCurvatureCoeff
  exact le_trans hcurv' (by nlinarith [hscaled])

end Synthesis
