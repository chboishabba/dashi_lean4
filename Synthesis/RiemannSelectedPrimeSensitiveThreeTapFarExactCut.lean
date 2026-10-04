import Synthesis.RiemannSelectedPrimeSensitiveThreeTapPaidCostCut
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdaptiveOffOrdWeld

/-!
# Literal reflection-tail normal form for the three-tap paid cost

The previous max-cut reduced the resonance sign to

  FarExact + Compensation.

The off-ordinate weld already identifies the complete transformed off-ordinate
carrier with one half of a summable reflection-pair tsum.  Since FarExact is
literally offOrd minus LocalExact, this file removes the final abstract `FarExact`
name from the analytic frontier.

No sign is asserted.  The remaining theorem is now a comparison between the
literal signed reflection-pair tail and the already-paid local/archimedean
compensation.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators

/-- Exact source-native normal form for the signed adaptive far term. -/
theorem QuarticFourSignedPolePair.threeTapAdaptiveFarExact_eq_half_pair_tsum_sub_local
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapAdaptiveFarExact eps
      =
    (1/2 : ℝ) *
      ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        W.threeTapAdaptivePairTerm eps (sigma : Zeros)
      - W.threeTapAdaptiveLocalExact eps := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveFarExact
  rw [W.threeTap_offOrd_eq_half_adaptivePair_tsum ht]

/-- The complete paid resonance cost written only in literal tail, local exact,
and the named non-far compensation. -/
theorem QuarticFourSignedPolePair.threeTapResonancePaidCost_eq_pair_tsum
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapResonancePaidCost eps
      =
    (1/2 : ℝ) *
      ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        W.threeTapAdaptivePairTerm eps (sigma : Zeros)
      - W.threeTapAdaptiveLocalExact eps
      + W.threeTapResonanceCompensation eps := by
  rw [W.threeTapResonancePaidCost_eq_far_add_compensation,
      W.threeTapAdaptiveFarExact_eq_half_pair_tsum_sub_local ht]

/-- PASS is exactly strict domination of the literal signed tail by the paid
local/archimedean threshold. -/
theorem QuarticFourSignedPolePair.threeTapResonancePaidCost_neg_iff_pair_tsum_lt
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapResonancePaidCost eps < 0
      ↔
    (1/2 : ℝ) *
      ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        W.threeTapAdaptivePairTerm eps (sigma : Zeros)
      < W.threeTapAdaptiveLocalExact eps
          - W.threeTapResonanceCompensation eps := by
  rw [W.threeTapResonancePaidCost_eq_pair_tsum ht]
  linarith

/-- Weak FAIL-side comparison in the literal reflection-tail coordinate. -/
theorem QuarticFourSignedPolePair.threeTapResonancePaidCost_nonneg_iff_pair_tsum_ge
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapResonancePaidCost eps
      ↔
    W.threeTapAdaptiveLocalExact eps
        - W.threeTapResonanceCompensation eps
      <=
    (1/2 : ℝ) *
      ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        W.threeTapAdaptivePairTerm eps (sigma : Zeros) := by
  rw [W.threeTapResonancePaidCost_eq_pair_tsum ht]
  linarith

/-- Strict constant-term FAIL comparison. -/
theorem QuarticFourSignedPolePair.threeTapResonancePaidCost_pos_iff_pair_tsum_gt
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    0 < W.threeTapResonancePaidCost eps
      ↔
    W.threeTapAdaptiveLocalExact eps
        - W.threeTapResonanceCompensation eps
      <
    (1/2 : ℝ) *
      ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        W.threeTapAdaptivePairTerm eps (sigma : Zeros) := by
  rw [W.threeTapResonancePaidCost_eq_pair_tsum ht]
  linarith

/-- The equality locus on which J2 becomes relevant. -/
theorem QuarticFourSignedPolePair.threeTapResonancePaidCost_eq_zero_iff_pair_tsum_eq
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.threeTapResonancePaidCost eps = 0
      ↔
    (1/2 : ℝ) *
      ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        W.threeTapAdaptivePairTerm eps (sigma : Zeros)
      = W.threeTapAdaptiveLocalExact eps
          - W.threeTapResonanceCompensation eps := by
  rw [W.threeTapResonancePaidCost_eq_pair_tsum ht]
  constructor <;> intro h <;> linarith

/-- Direct near-line PASS compiler from the literal reflection-tail inequality. -/
theorem QuarticFourSignedPolePair.exists_threeTapResonantTerminalProfile_pos_right_of_pair_tsum_lt
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (htail :
      (1/2 : ℝ) *
        ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          W.threeTapAdaptivePairTerm eps (sigma : Zeros)
        < W.threeTapAdaptiveLocalExact eps
            - W.threeTapResonanceCompensation eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        0 < W.threeTapAdaptiveTerminalProfile eps mult a := by
  apply W.exists_threeTapResonantTerminalProfile_pos_right_of_paidCost_neg
    ht hphase
  exact (W.threeTapResonancePaidCost_neg_iff_pair_tsum_lt ht).2 htail

/-- Direct strict near-line FAIL compiler from the opposite literal-tail
comparison. -/
theorem QuarticFourSignedPolePair.exists_threeTapResonantTerminalProfile_neg_right_of_pair_tsum_gt
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
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        W.threeTapAdaptiveTerminalProfile eps mult a < 0 := by
  apply W.exists_threeTapResonantTerminalProfile_neg_right_of_paidCost_pos
    ht hphase
  exact (W.threeTapResonancePaidCost_pos_iff_pair_tsum_gt ht).2 htail

end Synthesis
