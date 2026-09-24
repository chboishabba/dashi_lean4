import Synthesis.RiemannPoleWindowIntegralDeweighting
import Synthesis.RiemannFinalLiteralComplementSignedReduction

/-!
# Radius-zero pole correction on the final even cone

At sample radius zero the odd pole response vanishes and the even cone functional
reads the pole vector exactly as

    ell(Q_pole(0)) = -4 * poleEvenResp(g,t,0).

Thus a positive unweighted pole response gives a strictly negative pole
correction in the radius-zero explicit-formula balance.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone

theorem poleOddResp_zero_radius (g : ℝ → ℝ) (t : ℝ) :
    poleOddResp g t 0 = 0 := by
  unfold poleOddResp
  simp

theorem evenConeFunctional_poleVec_radiusZero {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t : ℝ) :
    evenConeFunctional (poleVec (sampleFam g t 0))
      = -4 * poleEvenResp g t 0 := by
  rw [poleVec_sampleFam hg hgc heven t 0]
  rw [map_smul]
  simp only [smul_eq_mul, poleParityVec, zero_mul,
    poleOddResp_zero_radius, evenConeFunctional_oddPattern,
    evenConeFunctional_evenPattern]
  ring

theorem radiusZero_pole_correction_negative_of_unweighted_positive
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    {t : ℝ}
    (hEc0 : 0 < poleEvenResp g t 0) :
    evenConeFunctional (poleVec (sampleFam g t 0)) < 0 := by
  rw [evenConeFunctional_poleVec_radiusZero hg hgc heven t]
  linarith

theorem radiusZero_signed_complement_lt_cluster_of_unweighted_pole_positive
    {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hshort : ∀ u, g u ≠ 0 → |u| < Real.log 2)
    {t : ℝ}
    (hEc0 : 0 < poleEvenResp g t 0) :
    -(finalLiteralComplement g t 0)
      < evenConeFunctional (clusterVec (sampleFam g t 0) t) := by
  have hbal := radiusZero_literal_complement_with_pole hgs hgc hshort t
  have hpole :=
    radiusZero_pole_correction_negative_of_unweighted_positive
      hgs.continuous hgc heven hEc0
  linarith

end Synthesis
