import Synthesis.RiemannFinalLiteralComplementSignedReduction
import Synthesis.RiemannQuantitativeCanonicalTaper
import Zeta23Bridge.LiteralWeilPrimeEvenCone

/-!
# Selected-radius pole annihilation and direct cluster reduction

The older radius-zero reduction retained a pole correction because the canonical
taper is constructed to kill the pole at the selected sample radius r, not at
r=0.

For an even taper g, however, the final even-cone functional annihilates the
odd pole pattern at every radius.  Hence

  ell(poleVec(sampleFam g t r)) = -4 * poleEvenResp g t r.

Therefore any pole-killing radius makes the complete pole channel vanish under
the exact consumer.  If the taper is also short enough to kill the prime
channel, the literal explicit formula gives the exact selected-radius identity

  finalLiteralComplement g t r
    = - ell(clusterVec(sampleFam g t r,t)).

This removes Gamma/RvM bookkeeping entirely from the sign reduction at the
selected radius.  The only remaining analytic sign input is positivity of the
same-ordinate cluster.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilPrimeEvenCone

theorem evenConeFunctional_poleVec
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t r : ℝ) :
    evenConeFunctional (poleVec (sampleFam g t r))
      = -4 * poleEvenResp g t r := by
  rw [poleVec_sampleFam hg hgc heven t r]
  rw [map_smul]
  simp only [smul_eq_mul, poleParityVec,
    evenConeFunctional_oddPattern,
    evenConeFunctional_evenPattern]
  ring

theorem evenConeFunctional_poleVec_eq_zero_of_poleEven_zero
    {g : ℝ → ℝ}
    (hg : Continuous g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    {t r : ℝ}
    (hkill : poleEvenResp g t r = 0) :
    evenConeFunctional (poleVec (sampleFam g t r)) = 0 := by
  rw [evenConeFunctional_poleVec hg hgc heven t r, hkill]
  ring

/--
Exact selected-radius reduction.  Prime invisibility plus pole annihilation
turns the signed literal complement into minus the same-ordinate cluster.
-/
theorem selectedRadius_literalComplement_eq_neg_cluster
    {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hshort : ∀ u, g u ≠ 0 → |u| < Real.log 2)
    {t r : ℝ}
    (hkill : poleEvenResp g t r = 0) :
    finalLiteralComplement g t r
      =
    - evenConeFunctional
        (clusterVec (sampleFam g t r) t) := by
  have hprime : primeVec (sampleFam g t r) = 0 :=
    primeVec_eq_zero_of_short_taper hshort t r
  have hpole :
      evenConeFunctional (poleVec (sampleFam g t r)) = 0 :=
    evenConeFunctional_poleVec_eq_zero_of_poleEven_zero
      hgs.continuous hgc heven hkill
  have hkd := fun i => sampleFam_contDiff hgs t r i
  have hkc := fun i => sampleFam_hasCompactSupport hgc t r i
  have hbal := literalWeilOrdinateFibreBalance hkd hkc t
  have hlin :
      evenConeFunctional (clusterVec (sampleFam g t r) t)
        + evenConeFunctional (offOrdVec (sampleFam g t r) t)
        + evenConeFunctional (primeVec (sampleFam g t r))
        + evenConeFunctional (gammaVec (sampleFam g t r))
        + evenConeFunctional (poleVec (sampleFam g t r)) = 0 := by
    rw [← map_add, ← map_add, ← map_add, ← map_add, hbal, map_zero]
  rw [hprime, map_zero, add_zero, hpole, add_zero] at hlin
  unfold finalLiteralComplement
  linarith

theorem selectedRadius_literalComplement_lt_zero_of_cluster_pos
    {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hshort : ∀ u, g u ≠ 0 → |u| < Real.log 2)
    {t r : ℝ}
    (hkill : poleEvenResp g t r = 0)
    (hcluster :
      0 <
      evenConeFunctional
        (clusterVec (sampleFam g t r) t)) :
    finalLiteralComplement g t r < 0 := by
  rw [selectedRadius_literalComplement_eq_neg_cluster
    hgs hgc heven hshort hkill]
  linarith

end Synthesis
