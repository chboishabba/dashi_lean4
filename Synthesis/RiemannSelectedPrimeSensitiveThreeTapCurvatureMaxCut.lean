import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAlphaStripWeld
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapFarDecay

/-!
# Canonical alpha-strip curvature max-cut

The per-zero far theorem already gives

  adverse(rho)
    <= mult(rho) * Curv(eps, alpha_rho) / (gamma_rho-t)^2.

The zeta critical strip gives |alpha_rho| <= 8/t, hence for t>=200

  |alpha_rho| <= 1/25.

This file isolates the highest-information analytic obligation as a uniform
bound for the *actual* oscillatory curvature on that fixed compact alpha strip.
Once such a bound C is paid, every adverse pair immediately has the clean
inverse-square majorant

  adverse(rho) <= mult(rho) * C / (gamma_rho-t)^2.

No witness-width or curvature estimate is manufactured here.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators

/-- Fixed alpha radius containing every normalized zeta horizontal displacement
in the high-t regime t>=200. -/
def threeTapHighAlphaRadius : ℝ := 1/25

theorem threeTapHighAlphaRadius_pos :
    0 < threeTapHighAlphaRadius := by
  unfold threeTapHighAlphaRadius
  norm_num

/-- The canonical zeta alpha radius 8/t is contained in [-1/25,1/25] for
t>=200. -/
theorem threeTapCanonicalAlphaRadius_le_highAlphaRadius
    {t : ℝ} (ht : 200 <= t) :
    threeTapCanonicalAlphaRadius t <= threeTapHighAlphaRadius := by
  have htpos : 0 < t := by linarith
  unfold threeTapCanonicalAlphaRadius threeTapHighAlphaRadius
  rw [div_le_iff₀ htpos]
  norm_num
  linarith

/-- Exact analytic obligation: bound the already-defined L1 second-derivative
curvature uniformly on the canonical compact alpha strip. -/
def QuarticFourSignedPolePair.ThreeTapUniformCurvatureBound
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps C : ℝ) : Prop :=
  0 <= C ∧
  ∀ alpha : ℝ,
    |alpha| <= threeTapHighAlphaRadius ->
      W.threeTapPairOscillatoryCurvature eps alpha <= C

/-- A paid compact-strip curvature bound controls the actual alpha attached to
every zeta zero. -/
theorem QuarticFourSignedPolePair.threeTapPairOscillatoryCurvature_le_of_uniform
    {t eps C : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hcurv : W.ThreeTapUniformCurvatureBound eps C)
    (rho : Zeros) :
    W.threeTapPairOscillatoryCurvature eps
        (heightOf rho / (t/16))
      <= C := by
  apply hcurv.2
  have hcanon := W.abs_normalized_height_le_canonicalAlphaRadius
    (by linarith : 0 < t) rho
  exact hcanon.trans (threeTapCanonicalAlphaRadius_le_highAlphaRadius ht)

/-- Once the compact-alpha curvature max-cut is paid, the actual adverse pair
has a witness-independent inverse-square majorant for that selected witness. -/
theorem QuarticFourSignedPolePair.threeTapPairAdversePart_le_uniformInverseSquare
    {t eps C : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hcurv : W.ThreeTapUniformCurvatureBound eps C)
    (rho : Zeros)
    (hord : ((rho : ℂ).im - t) ≠ 0) :
    W.threeTapPairAdversePart eps rho
      <=
    ((Zeta23.zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * C / (((rho : ℂ).im - t)^2) := by
  have hbase := W.threeTapPairAdversePart_le_inverseSquare
    ht rho hord (eps:=eps)
  have hC := W.threeTapPairOscillatoryCurvature_le_of_uniform
    ht hcurv rho
  have hm :
      0 <= ((Zeta23.zetaZeroConfig).mult (rho : ℂ) : ℝ) := by
    positivity
  have hd : 0 < (((rho : ℂ).im - t)^2) := sq_pos_of_ne_zero hord
  calc
    W.threeTapPairAdversePart eps rho
      <= ((Zeta23.zetaZeroConfig).mult (rho : ℂ) : ℝ)
          * W.threeTapPairOscillatoryCurvature eps
              (heightOf rho / (t/16))
          / (((rho : ℂ).im - t)^2) := hbase
    _ <= ((Zeta23.zetaZeroConfig).mult (rho : ℂ) : ℝ)
          * C / (((rho : ℂ).im - t)^2) := by
      apply div_le_div_of_nonneg_right _ hd.le
      exact mul_le_mul_of_nonneg_left hC hm

end Synthesis
