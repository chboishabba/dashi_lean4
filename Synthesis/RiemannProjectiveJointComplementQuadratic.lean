import Zeta23Bridge.LiteralWeilGammaProjectiveBound

/-!
# Joint projective Off + Gamma quadratic envelope

The vendored Zeta23Bridge source separately proves that the off-ordinate
projective defect and the Gamma projective defect are O(r^2) on the same
projective taper.  This file composes those theorem-bearing estimates without
changing carriers or introducing a new taper.

This is a donor theorem only.  The final DASHI RH lane currently uses the
universal pole-quotient taper, which is not definitionally identified with this
rank-two/projective taper.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilOffOrdinateTail
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilProjectiveStripConstant
open Zeta23Bridge.LiteralWeilOffOrdinateProjectiveTail
open Zeta23Bridge.LiteralWeilGammaProjectiveBound

/-- There is an absolute Gamma coefficient such that the combined projective
Off+Gamma defect is quadratically small in the sampling radius.  The Off
coefficient remains explicit through the same projective strip coefficient and
the exact off-ordinate weight. -/
theorem exists_jointProjectiveComplementQuadraticEnvelope :
    ∃ CG : ℝ, 0 ≤ CG ∧
      ∀ {g : ℝ → ℝ} {Λ : ℝ}, ContDiff ℝ 2 g → (∀ u, g (-u) = g u) →
        (∀ u, g u ≠ 0 → |u| ≤ Λ) → 0 ≤ Λ → ∀ t r : ℝ,
          |offOrdProjectiveDefect g t r + gammaProjectiveDefect g t r|
            ≤ r ^ 2 *
              (4 * projStripCoeff g Λ t * offOrdWeight t
                + projStripCoeff g Λ t * CG) := by
  obtain ⟨CG, hCG0, hGamma⟩ := exists_gammaProjectiveEnvelope
  refine ⟨CG, hCG0, ?_⟩
  intro g Λ hgs heven hsupp hΛ t r
  have hgc : HasCompactSupport g := hasCompactSupport_of_radius hsupp
  have hOffRaw :=
    offOrdProjectiveTailEnvelope hgs hgc heven hsupp hΛ t r
  have hStrip :=
    stripConst_projTaper_le hgs hsupp hΛ t r
  have hW : 0 ≤ offOrdWeight t := offOrdWeight_nonneg t
  have hP : 0 ≤ projStripCoeff g Λ t := by
    unfold projStripCoeff
    positivity
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hOff :
      |offOrdProjectiveDefect g t r|
        ≤ r ^ 2 * (4 * projStripCoeff g Λ t * offOrdWeight t) := by
    have hmul :
        4 * stripConst (sampleTest (projTaper g r) t 0) Λ * offOrdWeight t
          ≤ 4 * (r ^ 2 * projStripCoeff g Λ t) * offOrdWeight t := by
      have hs :=
        mul_le_mul_of_nonneg_right hStrip hW
      nlinarith
    calc
      |offOrdProjectiveDefect g t r|
          ≤ 4 * stripConst (sampleTest (projTaper g r) t 0) Λ * offOrdWeight t :=
        hOffRaw
      _ ≤ 4 * (r ^ 2 * projStripCoeff g Λ t) * offOrdWeight t := hmul
      _ = r ^ 2 * (4 * projStripCoeff g Λ t * offOrdWeight t) := by ring
  have hGamma :=
    hGamma hgs heven hsupp hΛ t r
  have htri :=
    abs_add_le
      (offOrdProjectiveDefect g t r)
      (gammaProjectiveDefect g t r)
  have hsum :
      |offOrdProjectiveDefect g t r + gammaProjectiveDefect g t r|
        ≤ r ^ 2 * (4 * projStripCoeff g Λ t * offOrdWeight t)
          + r ^ 2 * (projStripCoeff g Λ t * CG) := by
    exact le_trans htri (add_le_add hOff hGamma)
  calc
    |offOrdProjectiveDefect g t r + gammaProjectiveDefect g t r|
        ≤ r ^ 2 * (4 * projStripCoeff g Λ t * offOrdWeight t)
          + r ^ 2 * (projStripCoeff g Λ t * CG) := hsum
    _ = r ^ 2 *
        (4 * projStripCoeff g Λ t * offOrdWeight t
          + projStripCoeff g Λ t * CG) := by ring

end Synthesis
