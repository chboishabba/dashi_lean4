import Synthesis.RiemannSelectedPrimeSensitiveThreeTapFarExactCut

/-!
# Globalizing a one-scale near-line PASS across the full displacement strip

A resonance PASS from the max-cut is local in horizontal displacement:

  0 < a < delta.

For a zero in the critical strip the remaining geometric range is

  delta <= a <= 1/2.

This file contains only the exact interval glue.  It does not manufacture the
compact-away-from-zero lower bound; that is deliberately exposed as the next
analytic input.
-/

noncomputable section
namespace Synthesis

open scoped Real

/-- Positivity of the transformed terminal profile for every admissible
positive off-line displacement. -/
def QuarticFourSignedPolePair.ThreeTapAllOffLineDisplacementsPositive
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps mult : ℝ) : Prop :=
  ∀ a : ℝ, 0 < a → a <= (1/2 : ℝ) →
    0 < W.threeTapAdaptiveTerminalProfile eps mult a

/-- The compact-away-from-zero part of the displacement problem for a chosen
near-line radius. -/
def QuarticFourSignedPolePair.ThreeTapMidStripPositive
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps mult delta : ℝ) : Prop :=
  ∀ a : ℝ, delta <= a → a <= (1/2 : ℝ) →
    0 < W.threeTapAdaptiveTerminalProfile eps mult a

/-- Exact interval glue.  Equality `a = delta` belongs to the mid-strip side,
so there is no endpoint gap. -/
theorem QuarticFourSignedPolePair.threeTap_globalize_near_and_mid
    {t eps mult delta : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hnear :
      ∀ a : ℝ, 0 < a → a < delta →
        0 < W.threeTapAdaptiveTerminalProfile eps mult a)
    (hmid : W.ThreeTapMidStripPositive eps mult delta) :
    W.ThreeTapAllOffLineDisplacementsPositive eps mult := by
  intro a ha haHalf
  by_cases had : a < delta
  · exact hnear a ha had
  · exact hmid a (le_of_not_gt had) haHalf

/-- A uniform positive lower margin on the compact strip is sufficient for the
mid-strip positivity premise. -/
theorem QuarticFourSignedPolePair.threeTapMidStripPositive_of_uniform_margin
    {t eps mult delta c : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hc : 0 < c)
    (hmargin :
      ∀ a : ℝ, delta <= a → a <= (1/2 : ℝ) →
        c <= W.threeTapAdaptiveTerminalProfile eps mult a) :
    W.ThreeTapMidStripPositive eps mult delta := by
  intro a had haHalf
  exact lt_of_lt_of_le hc (hmargin a had haHalf)

/-- A near-line existence theorem plus a mid-strip provider for the radius it
returns yields positivity on every positive displacement up to one half.

The provider is quantified over positive radii because the near-line theorem
chooses its radius existentially.  A future quantitative near-line theorem may
replace this with a concrete radius and a single compact-strip estimate. -/
theorem QuarticFourSignedPolePair.threeTap_globalize_of_exists_near
    {t eps mult : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hnear :
      ∃ delta : ℝ, 0 < delta ∧
        ∀ a : ℝ, 0 < a → a < delta →
          0 < W.threeTapAdaptiveTerminalProfile eps mult a)
    (hmid :
      ∀ delta : ℝ, 0 < delta →
        W.ThreeTapMidStripPositive eps mult delta) :
    W.ThreeTapAllOffLineDisplacementsPositive eps mult := by
  obtain ⟨delta, hdelta, hband⟩ := hnear
  exact W.threeTap_globalize_near_and_mid hband (hmid delta hdelta)

/-- Direct globalization of the strict literal-tail resonance PASS, conditional
only on the compact mid-strip theorem. -/
theorem QuarticFourSignedPolePair.threeTap_globalize_of_pair_tsum_lt
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (htail :
      (1/2 : ℝ) *
        ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          W.threeTapAdaptivePairTerm eps (sigma : Zeros)
        < W.threeTapAdaptiveLocalExact eps
            - W.threeTapResonanceCompensation eps)
    (hmid :
      ∀ delta : ℝ, 0 < delta →
        W.ThreeTapMidStripPositive eps mult delta) :
    W.ThreeTapAllOffLineDisplacementsPositive eps mult := by
  apply W.threeTap_globalize_of_exists_near
  · exact W.exists_threeTapResonantTerminalProfile_pos_right_of_pair_tsum_lt
      ht hphase htail
  · exact hmid

/-- Uniform-margin version of the globalization consumer. -/
theorem QuarticFourSignedPolePair.threeTap_globalize_of_pair_tsum_lt_uniform_mid
    {t eps mult c : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (htail :
      (1/2 : ℝ) *
        ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          W.threeTapAdaptivePairTerm eps (sigma : Zeros)
        < W.threeTapAdaptiveLocalExact eps
            - W.threeTapResonanceCompensation eps)
    (hc : 0 < c)
    (hmargin :
      ∀ delta : ℝ, 0 < delta →
        ∀ a : ℝ, delta <= a → a <= (1/2 : ℝ) →
          c <= W.threeTapAdaptiveTerminalProfile eps mult a) :
    W.ThreeTapAllOffLineDisplacementsPositive eps mult := by
  apply W.threeTap_globalize_of_pair_tsum_lt ht hphase htail
  intro delta hdelta
  exact W.threeTapMidStripPositive_of_uniform_margin hc
    (hmargin delta hdelta)

end Synthesis
