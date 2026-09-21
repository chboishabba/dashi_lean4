import Synthesis.RiemannHighProjectiveFrontier
import Zeta23Bridge.LiteralWeilDeterministicSchurMarginInstance

/-!
# Prize-facing high Schur frontier

The one-radius selected complement is now strictly negative at every actual zero
in the high regime, but that observable is height-blind.  The scalar two-radius
projective envelope is height-sensitive, but its absolute-majorant gate is
already known to be quantitatively dead at large ordinates.

The next sound prize-facing consumer is therefore the exact three-taper Schur
quotient already present in the literal Zeta23 bridge.

For three short even tapers, exact elimination of the deterministic pole and
Gamma projective vectors gives

  elim2 pole gamma cluster = elim2 pole gamma offOrd.

Hence an off-line zero is impossible whenever a theorem-bearing producer gives

  margin <= ||elim2 pole gamma cluster||^2
  ||elim2 pole gamma offOrd||^2 < margin.

This file packages exactly that witness and compiles it to the critical-line
conclusion.  It does not assert the remaining projected far-tail inequality.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.MultiTaperSchurCore
open Zeta23Bridge.LiteralWeilDeterministicProjectiveSchur
open Zeta23Bridge.LiteralWeilDeterministicSchurMarginInstance

/--
The exact high-side Schur payment for one putative off-line zero.

All representation, prime-invisibility, and deterministic nuisance-elimination
premises are carried on the same literal three-taper family.
-/
structure HighSchurWitness (t : ℝ) where
  g : Fin 3 → ℝ → ℝ
  r : ℝ
  margin : ℝ

  smooth : ∀ j, ContDiff ℝ 2 (g j)
  compact : ∀ j, HasCompactSupport (g j)
  even : ∀ j u, g j (-u) = g j u
  short : ∀ j u, g j u ≠ 0 → |u| < Real.log 2

  poleIndependent : poleVec3 g t r ≠ 0
  gammaIndependent : perp2 (poleVec3 g t r) (gammaVec3 g t r) ≠ 0

  margin_le_survivingCluster :
    margin ≤
      det3 (poleVec3 g t r) (gammaVec3 g t r) (clusterVec3 g t r) ^ 2
        / wedgeSq (poleVec3 g t r) (gammaVec3 g t r)

  projectedOffOrd_below_margin :
    normSqP (offOrdVec3 g t r) < margin

/-- A completed high Schur witness is inconsistent with the literal balance. -/
theorem false_of_highSchurWitness {t : ℝ} (w : HighSchurWitness t) : False := by
  exact literal_false_of_offOrd_energy_below_margin
    w.g t w.r
    w.smooth w.compact w.even w.short
    w.poleIndependent w.gammaIndependent
    w.margin w.margin_le_survivingCluster
    w.projectedOffOrd_below_margin

/--
Prize-facing high contradiction compiler.

The analytic producer is asked for a Schur witness only under the off-line
hypothesis.  No selected-radius sign is promoted to a height detector.
-/
theorem high_zero_on_criticalLine_of_schurProducer
    {rhoStar : Zeros} {t : ℝ}
    (him : (rhoStar : ℂ).im = t)
    (ht : 18 ≤ t)
    (producer : heightOf rhoStar ≠ 0 → HighSchurWitness t) :
    heightOf rhoStar = 0 := by
  by_contra hoff
  exact false_of_highSchurWitness (producer hoff)

/-- The same high compiler in the theorem-facing real-part form. -/
theorem high_zero_realPart_eq_half_of_schurProducer
    {rhoStar : Zeros} {t : ℝ}
    (him : (rhoStar : ℂ).im = t)
    (ht : 18 ≤ t)
    (producer : heightOf rhoStar ≠ 0 → HighSchurWitness t) :
    (rhoStar : ℂ).re = 1 / 2 := by
  have h := high_zero_on_criticalLine_of_schurProducer him ht producer
  unfold heightOf at h
  linarith

/--
A norm-form producer interface.  This is often easier for subsequent analytic
work than the determinant-ratio spelling of the surviving margin.
-/
structure HighSchurNormWitness (t : ℝ) where
  g : Fin 3 → ℝ → ℝ
  r : ℝ
  margin : ℝ

  smooth : ∀ j, ContDiff ℝ 2 (g j)
  compact : ∀ j, HasCompactSupport (g j)
  even : ∀ j u, g j (-u) = g j u
  short : ∀ j u, g j u ≠ 0 → |u| < Real.log 2

  poleIndependent : poleVec3 g t r ≠ 0
  gammaIndependent : perp2 (poleVec3 g t r) (gammaVec3 g t r) ≠ 0

  margin_le_projectedCluster :
    margin ≤ normSqP
      (elim2 (poleVec3 g t r) (gammaVec3 g t r) (clusterVec3 g t r))

  projectedOffOrd_below_margin :
    normSqP
      (elim2 (poleVec3 g t r) (gammaVec3 g t r) (offOrdVec3 g t r))
      < margin

/-- The direct norm form closes by the exact Schur balance itself. -/
theorem false_of_highSchurNormWitness
    {t : ℝ} (w : HighSchurNormWitness t) : False := by
  exact false_of_signedOffOrd_below_survivingCluster
    w.g t w.r
    w.smooth w.compact w.even w.short
    w.poleIndependent w.gammaIndependent
    w.margin w.margin_le_projectedCluster
    w.projectedOffOrd_below_margin

theorem high_zero_realPart_eq_half_of_schurNormProducer
    {rhoStar : Zeros} {t : ℝ}
    (him : (rhoStar : ℂ).im = t)
    (ht : 18 ≤ t)
    (producer : heightOf rhoStar ≠ 0 → HighSchurNormWitness t) :
    (rhoStar : ℂ).re = 1 / 2 := by
  by_contra hre
  have hoff : heightOf rhoStar ≠ 0 := by
    intro hzero
    apply hre
    unfold heightOf at hzero
    linarith
  exact false_of_highSchurNormWitness (producer hoff)

end Synthesis
