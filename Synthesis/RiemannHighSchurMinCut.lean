import Synthesis.RiemannHighSchurFrontier
import Synthesis.RiemannShortWindowSchurCompiler

/-!
# Current RH high-side Schur min-cut

The high contradiction has now moved beyond both obsolete scalar routes:

* the one-radius selected complement is exact and negative, but height-blind;
* the scalar projective absolute-envelope gate is height-sensitive, but its
  large-ordinate majorization is known to be quantitatively inadequate.

The theorem-facing high payment is therefore split on one shared literal
three-taper substrate into exactly two producers:

1. geometry: short/even/smooth tapers, pole/Gamma independence, and a positive
   surviving projected cluster margin;
2. signed far-tail analysis: the Schur-projected off-ordinate zero energy lies
   strictly below that same margin.

This module makes that factorization exact and compiles the two producers back
to the prize-facing critical-line conclusion.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.MultiTaperSchurCore
open Zeta23Bridge.LiteralWeilDeterministicProjectiveSchur

/-- Shared literal substrate for the final high Schur comparison. -/
structure HighSchurSubstrate (t : ℝ) where
  g : Fin 3 → ℝ → ℝ
  r : ℝ
  smooth : ∀ j, ContDiff ℝ 2 (g j)
  compact : ∀ j, HasCompactSupport (g j)
  even : ∀ j u, g j (-u) = g j u
  short : ∀ j u, g j u ≠ 0 → |u| < Real.log 2
  poleIndependent : poleVec3 g t r ≠ 0
  gammaIndependent : perp2 (poleVec3 g t r) (gammaVec3 g t r) ≠ 0

/-- Geometry/signal producer: a strict margin surviving exact nuisance removal. -/
structure HighSchurGeometry {t : ℝ} (S : HighSchurSubstrate t) where
  margin : ℝ
  margin_pos : 0 < margin
  margin_le_projectedCluster :
    margin ≤ normSqP
      (elim2 (poleVec3 S.g t S.r) (gammaVec3 S.g t S.r)
        (clusterVec3 S.g t S.r))

/-- Signed zero-distribution producer on exactly the same substrate and margin. -/
structure HighSchurFarTail {t : ℝ} (S : HighSchurSubstrate t)
    (G : HighSchurGeometry S) where
  projectedOffOrd_below_margin :
    normSqP
      (elim2 (poleVec3 S.g t S.r) (gammaVec3 S.g t S.r)
        (offOrdVec3 S.g t S.r))
      < G.margin

/-- The split min-cut compiles definition-for-definition to the terminal witness. -/
def highSchurNormWitnessOfPayments
    {t : ℝ} (S : HighSchurSubstrate t)
    (G : HighSchurGeometry S) (F : HighSchurFarTail S G) :
    HighSchurNormWitness t where
  g := S.g
  r := S.r
  margin := G.margin
  smooth := S.smooth
  compact := S.compact
  even := S.even
  short := S.short
  poleIndependent := S.poleIndependent
  gammaIndependent := S.gammaIndependent
  margin_le_projectedCluster := G.margin_le_projectedCluster
  projectedOffOrd_below_margin := F.projectedOffOrd_below_margin

theorem false_of_highSchurPayments
    {t : ℝ} (S : HighSchurSubstrate t)
    (G : HighSchurGeometry S) (F : HighSchurFarTail S G) : False :=
  false_of_highSchurNormWitness (highSchurNormWitnessOfPayments S G F)

/--
Final high-region compiler: under an off-line hypothesis, one shared Schur
substrate plus the geometry and signed-far-tail payments force the zero back to
the critical line.
-/
theorem high_zero_realPart_eq_half_of_schurPayments
    {rhoStar : Zeros} {t : ℝ}
    (him : (rhoStar : ℂ).im = t)
    (ht : 18 ≤ t)
    (substrate : heightOf rhoStar ≠ 0 → HighSchurSubstrate t)
    (geometry :
      ∀ hoff : heightOf rhoStar ≠ 0,
        HighSchurGeometry (substrate hoff))
    (farTail :
      ∀ hoff : heightOf rhoStar ≠ 0,
        HighSchurFarTail (substrate hoff) (geometry hoff)) :
    (rhoStar : ℂ).re = 1 / 2 := by
  by_contra hre
  have hoff : heightOf rhoStar ≠ 0 := by
    intro hz
    apply hre
    unfold heightOf at hz
    linarith
  exact false_of_highSchurPayments
    (substrate hoff) (geometry hoff) (farTail hoff)

/--
The remaining far-tail payment may equivalently be stated against the projected
cluster norm itself.  Any strict projected off-ordinate inequality immediately
manufactures a positive midpoint margin.
-/
theorem highSchurFarTail_of_strict_projected_comparison
    {t : ℝ} (S : HighSchurSubstrate t)
    (hcluster :
      0 < normSqP
        (elim2 (poleVec3 S.g t S.r) (gammaVec3 S.g t S.r)
          (clusterVec3 S.g t S.r)))
    (hstrict :
      normSqP
        (elim2 (poleVec3 S.g t S.r) (gammaVec3 S.g t S.r)
          (offOrdVec3 S.g t S.r))
        <
      normSqP
        (elim2 (poleVec3 S.g t S.r) (gammaVec3 S.g t S.r)
          (clusterVec3 S.g t S.r))) :
    ∃ G : HighSchurGeometry S, HighSchurFarTail S G := by
  let C := normSqP
    (elim2 (poleVec3 S.g t S.r) (gammaVec3 S.g t S.r)
      (clusterVec3 S.g t S.r))
  let O := normSqP
    (elim2 (poleVec3 S.g t S.r) (gammaVec3 S.g t S.r)
      (offOrdVec3 S.g t S.r))
  let M := (O + C) / 2
  have hMpos : 0 < M := by
    have hO0 : 0 ≤ O := normSqP_nonneg _
    dsimp [M, O, C]
    linarith
  have hMC : M ≤ C := by
    dsimp [M, O, C] at *
    linarith
  have hOM : O < M := by
    dsimp [M, O, C] at *
    linarith
  let G : HighSchurGeometry S :=
    { margin := M
      margin_pos := hMpos
      margin_le_projectedCluster := hMC }
  refine ⟨G, ?_⟩
  exact { projectedOffOrd_below_margin := hOM }

end Synthesis
