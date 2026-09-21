import Synthesis.RiemannFinalComplementCenteredQuadratic
import Zeta23Bridge.LiteralWeilGammaConeBound

/-!
# Final absolute-budget excess reduction

The centered estimates are useful for the contradiction only after returning to
the actual absolute budgets.  This file does exactly that.

For the final universal pole-quotient consumer,

  B_comp(r) := |D_off(r)| + |Q_Gamma(r)|,

the exact radius-centering identities imply

  B_comp(r)
    <= B_comp(0) + r^2 * E_center,

where

  B_comp(0) = |D_off(0)| + 2 |Gamma_g(t,0)|

and E_center is explicit in the centered strip coefficient, off-ordinate weight,
and one absolute Gamma-tail constant.

Thus the old shrinking-support Gamma problem is reduced to one explicit
height-free baseline allocation problem plus a quadratic correction.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilGammaConeBound
open Zeta23Bridge.LiteralWeilOffOrdinateTail

def radiusZeroComplementBudget (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  |evenConeFunctional (offOrdVec (sampleFam g t 0) t)|
    + 2 * |gammaResp g t 0|

theorem exists_finalComplementBudgetExcessReduction :
    ∃ CG : ℝ, 0 ≤ CG ∧
      ∀ {g : ℝ → ℝ} {Λ : ℝ},
        ContDiff ℝ 2 g →
        HasCompactSupport g →
        (∀ u, g (-u) = g u) →
        (∀ u, g u ≠ 0 → |u| ≤ Λ) →
        0 ≤ Λ →
        ∀ t r : ℝ,
          |evenConeFunctional (offOrdVec (sampleFam g t r) t)|
            + |evenConeFunctional (gammaVec (sampleFam g t r))|
          ≤ radiusZeroComplementBudget g t
            + r ^ 2 *
              (4 * gammaCenteredStripCoeff g Λ t * offOrdWeight t
                + 2 * CG * gammaCenteredStripCoeff g Λ t) := by
  obtain ⟨CG, hCG, hGamma⟩ := exists_centeredGammaQuadraticEnvelope
  refine ⟨CG, hCG, ?_⟩
  intro g Λ hgs hgc heven hsupp hΛ t r

  have hOffDiff :=
    abs_finalOffOrd_centered_le hgs heven hsupp hΛ t r
  have hOffTri :=
    abs_sub_abs_le_abs_sub
      (evenConeFunctional (offOrdVec (sampleFam g t r) t))
      (evenConeFunctional (offOrdVec (sampleFam g t 0) t))
  have hOffDir :
      |evenConeFunctional (offOrdVec (sampleFam g t r) t)|
        - |evenConeFunctional (offOrdVec (sampleFam g t 0) t)|
      ≤ |evenConeFunctional (offOrdVec (sampleFam g t r) t)
          - evenConeFunctional (offOrdVec (sampleFam g t 0) t)| :=
    le_trans (le_abs_self _) hOffTri
  have hOff :
      |evenConeFunctional (offOrdVec (sampleFam g t r) t)|
        ≤ |evenConeFunctional (offOrdVec (sampleFam g t 0) t)|
          + 4 * r ^ 2 * gammaCenteredStripCoeff g Λ t * offOrdWeight t := by
    linarith

  have hGammaId :=
    gammaResp_centered_radius hgs hgc heven hsupp hΛ t r
  have hGammaDef :=
    gammaConeValue_exact hgs.continuous hgc heven t r
  have hGammaCentered := hGamma hgs heven hsupp hΛ t r
  have hGammaCorr :
      |(gammaResp g t r + gammaResp g t (-r))
          - 2 * gammaResp g t 0|
        ≤ 2 * r ^ 2 * (CG * gammaCenteredStripCoeff g Λ t) := by
    rw [hGammaId, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    nlinarith
  have hGammaTri :=
    abs_sub_abs_le_abs_sub
      (gammaResp g t r + gammaResp g t (-r))
      (2 * gammaResp g t 0)
  have hGamma :
      |evenConeFunctional (gammaVec (sampleFam g t r))|
        ≤ 2 * |gammaResp g t 0|
          + 2 * r ^ 2 * (CG * gammaCenteredStripCoeff g Λ t) := by
    rw [hGammaDef, abs_neg]
    have htwo : |2 * gammaResp g t 0| = 2 * |gammaResp g t 0| := by
      rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    rw [htwo] at hGammaTri
    have hGammaDir :
        |gammaResp g t r + gammaResp g t (-r)|
          - 2 * |gammaResp g t 0|
        ≤ |(gammaResp g t r + gammaResp g t (-r))
            - 2 * gammaResp g t 0| :=
      le_trans (le_abs_self _) hGammaTri
    linarith

  unfold radiusZeroComplementBudget
  nlinarith [hOff, hGamma]

end Synthesis
