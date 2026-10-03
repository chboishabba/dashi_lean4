import Synthesis.RiemannSelectedPrimeSensitiveThreeTapFarExactCut
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapMaxCutClosure
import Synthesis.RiemannSelectedPrimeSensitiveTwoScale

/-!
# Clean promotion boundary from one-scale failure to the existing two-scale source

A strict one-scale near-line failure is now a mathematically meaningful trigger
to stop optimizing the one-frequency deformation.  The repository already owns
a two-scale source whose `log 2` and `log 3` samples are independent for the
selected narrow four-window profiles at t >= 300.

This file connects those facts without claiming that the two-scale completed
terminal scalar has already been paid.
-/

noncomputable section
namespace Synthesis

open scoped Real

/-- Strict local failure of the one-scale completed terminal profile. -/
def QuarticFourSignedPolePair.ThreeTapNearLineFails
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps mult : ℝ) : Prop :=
  ∃ delta : ℝ, 0 < delta ∧
    ∀ a : ℝ, 0 < a → a < delta →
      W.threeTapAdaptiveTerminalProfile eps mult a < 0

/-- Literal reflection-tail failure compiles to the named one-scale failure
surface. -/
theorem QuarticFourSignedPolePair.threeTapNearLineFails_of_pair_tsum_gt
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (htail :
      W.threeTapAdaptiveLocalExact eps
          - W.threeTapResonanceCompensation eps
        <
      (1/2 : ℝ) *
        ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          W.threeTapAdaptivePairTerm eps (sigma : Zeros)) :
    W.ThreeTapNearLineFails eps mult := by
  exact W.exists_threeTapResonantTerminalProfile_neg_right_of_pair_tsum_gt
    ht hphase htail

/-- On the balanced paid-cost locus, a certified positive smooth J2 is the
other strict one-scale failure mechanism. -/
theorem QuarticFourSignedPolePair.threeTapNearLineFails_of_balanced_J2_pos
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hmult : 0 < mult)
    (hcost : W.threeTapResonancePaidCost eps = 0)
    (hJ : 0 < W.threeTapNormalizedJ2Polynomial eps) :
    W.ThreeTapNearLineFails eps mult := by
  exact W.exists_threeTapResonantTerminalProfile_neg_right_of_paidCost_zero_J2_pos
    ht hphase hmult hcost hJ

/-- Atomic-margin version of the balanced failure trigger. -/
theorem QuarticFourSignedPolePair.threeTapNearLineFails_of_balanced_atomic_margin
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hmult : 0 < mult)
    (hcost : W.threeTapResonancePaidCost eps = 0)
    (hmargin :
      W.threeTapJ2PolynomialErrorEnvelope eps
        < W.threeTapAtomicJ2Polynomial eps) :
    W.ThreeTapNearLineFails eps mult := by
  exact
    W.exists_threeTapResonantTerminalProfile_neg_right_of_paidCost_zero_atomic_gt_errorEnvelope
      ht hphase hmult hcost hmargin

/-- Exact independent prime-2/prime-3 source data on both selected endpoint
detectors.  This is the reusable source made available after one-scale failure. -/
def QuarticFourSignedPolePair.TwoScaleEndpointSamples
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (e2 e3 : ℝ) : Prop :=
  (
    detectorTwoScale
        (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
        e2 e3 (Real.log 2)
      = e2 * quarticFourPhysicalDetector W.R (1/2) W.muHalf t 0
    ∧
    detectorTwoScale
        (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
        e2 e3 (Real.log 3)
      = e3 * quarticFourPhysicalDetector W.R (1/2) W.muHalf t 0
    ∧
    ∀ n : ℕ, 4 <= n →
      detectorTwoScale
          (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
          e2 e3 (Real.log n) = 0
  )
  ∧
  (
    detectorTwoScale
        (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
        e2 e3 (Real.log 2)
      = e2 * quarticFourPhysicalDetector W.R (2/3) W.muTwo t 0
    ∧
    detectorTwoScale
        (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
        e2 e3 (Real.log 3)
      = e3 * quarticFourPhysicalDetector W.R (2/3) W.muTwo t 0
    ∧
    ∀ n : ℕ, 4 <= n →
      detectorTwoScale
          (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
          e2 e3 (Real.log n) = 0
  )

theorem QuarticFourSignedPolePair.twoScaleEndpointSamples
    {t e2 e3 : ℝ}
    (ht : 300 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.TwoScaleEndpointSamples e2 e3 := by
  constructor
  · exact quarticFourPhysicalDetector_twoScale_samples
      W.Rpos W.RltOne ht
  · exact quarticFourPhysicalDetector_twoScale_samples
      W.Rpos W.RltOne ht

/-- Clean promotion theorem: once the one-scale mechanism is strictly negative,
the existing two-scale source is available with independent arithmetic samples.
No completed two-scale sign is claimed here. -/
theorem QuarticFourSignedPolePair.threeTapFail_promotes_twoScaleSource
    {t eps mult e2 e3 : ℝ}
    (ht : 300 <= t)
    (W : QuarticFourSignedPolePair t)
    (hfail : W.ThreeTapNearLineFails eps mult) :
    W.ThreeTapNearLineFails eps mult
      ∧ W.TwoScaleEndpointSamples e2 e3 := by
  exact ⟨hfail, W.twoScaleEndpointSamples ht⟩

/-- Direct promotion from a strict paid-cost/reflection-tail failure. -/
theorem QuarticFourSignedPolePair.pairTsumFail_promotes_twoScaleSource
    {t eps mult e2 e3 : ℝ}
    (ht : 300 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (htail :
      W.threeTapAdaptiveLocalExact eps
          - W.threeTapResonanceCompensation eps
        <
      (1/2 : ℝ) *
        ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          W.threeTapAdaptivePairTerm eps (sigma : Zeros)) :
    W.ThreeTapNearLineFails eps mult
      ∧ W.TwoScaleEndpointSamples e2 e3 := by
  apply W.threeTapFail_promotes_twoScaleSource ht
  exact W.threeTapNearLineFails_of_pair_tsum_gt (by linarith) hphase htail

end Synthesis
