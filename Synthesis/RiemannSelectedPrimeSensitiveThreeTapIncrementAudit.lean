import Synthesis.RiemannSelectedPrimeSensitiveThreeTapCompleted

/-!
# Three-tap exact completed increment and phase-resonance obstruction

All identities compare the SAME physical selected pole pair W at epsilon and
zero strength. No RH positivity hypothesis is introduced. In particular an
activated prime sample is not an independent positive completed margin.
-/

noncomputable section
namespace Synthesis

/-- Compare the complete four-channel Zeta23 projective formula at nonzero
tap strength with the very same source at zero tap strength. Every altered
channel, including Gamma, pole and off-ordinate, remains on the right. -/
theorem QuarticFourSignedPolePair.threeTap_completed_increment
    {t eps : ℝ}
    (ht : 200 ≤ t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.clusterHeightDefect
      - W.threeTapChannelCombination 0
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.clusterHeightDefect
    =
    (W.threeTapChannelCombination eps
       Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
     - W.threeTapChannelCombination 0
       Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect)
    + (W.threeTapSignedPrimeCombination eps
       - W.threeTapSignedPrimeCombination 0)
    + (W.threeTapChannelCombination eps
       Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect
     - W.threeTapChannelCombination 0
       Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect)
    + (W.threeTapChannelCombination eps
       Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
     - W.threeTapChannelCombination 0
       Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect) := by
  have he := W.threeTapCompletedCluster_eq_off_add_arithmetic ht (eps := eps)
  have hz := W.threeTapCompletedCluster_eq_off_add_arithmetic ht (eps := 0)
  unfold QuarticFourSignedPolePair.threeTapCompletedArithmetic at he hz
  linarith

/-- At any resonant height, the selected transformed prime *projective*
channel vanishes for every tap strength, while the other three completed
channels remain changed. Thus no positive lower bound can follow from
prime activation alone at such a height. -/
theorem QuarticFourSignedPolePair.threeTap_resonant_completed_increment
    {t eps : ℝ}
    (ht : 200 ≤ t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0) :
    W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.clusterHeightDefect
      - W.threeTapChannelCombination 0
      Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.clusterHeightDefect
    =
    (W.threeTapChannelCombination eps
       Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
     - W.threeTapChannelCombination 0
       Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect)
    + (W.threeTapChannelCombination eps
       Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect
     - W.threeTapChannelCombination 0
       Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect)
    + (W.threeTapChannelCombination eps
       Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
     - W.threeTapChannelCombination 0
       Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect) := by
  have h := W.threeTap_completed_increment ht
  have hp := W.threeTapSignedPrime_eq_zero_at_resonance ht hphase (eps := eps)
  have hp0 := W.threeTapSignedPrime_eq_zero_at_zeroStrength ht
  rw [hp, hp0] at h
  linarith

/-- A uniform positive lower bound for the prime projective term is
impossible on any height family containing a resonant physical witness. -/
theorem QuarticFourSignedPolePair.threeTap_no_uniform_positive_prime_margin
    {t eps delta : ℝ}
    (ht : 200 ≤ t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hdelta : 0 < delta) :
    ¬ delta ≤ W.threeTapSignedPrimeCombination eps := by
  rw [W.threeTapSignedPrime_eq_zero_at_resonance ht hphase]
  exact not_le.mpr hdelta

end Synthesis
