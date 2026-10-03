import Synthesis.RiemannSelectedPrimeSensitiveThreeTapMaxCutDecision

/-!
# Exact scalar cut for the paid three-tap resonance cost

The paid resonance cost is already

  FarExact + Gamma + Pole + 1/2 (LocalExact + LocalBudget).

This file names the non-far compensation and proves that the whole sign problem
is exactly one comparison between FarExact and minus that compensation.  No
termwise sign is assumed, and in particular no unshifted pole-sign theorem is
silently transferred to the translated detector.
-/

noncomputable section
namespace Synthesis

open scoped Real

def QuarticFourSignedPolePair.threeTapResonanceCompensation
    {t : ℝ} (W : QuarticFourSignedPolePair t) (eps : ℝ) : ℝ :=
  W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect
    +
  W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
    +
  (1/2 : ℝ) *
    (W.threeTapAdaptiveLocalExact eps
      + W.threeTapAdaptiveLocalBudget eps)

theorem QuarticFourSignedPolePair.threeTapResonancePaidCost_eq_far_add_compensation
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapResonancePaidCost eps
      = W.threeTapAdaptiveFarExact eps
        + W.threeTapResonanceCompensation eps := by
  rw [W.threeTapResonancePaidCost_eq_adaptive_far_local]
  unfold QuarticFourSignedPolePair.threeTapResonanceCompensation
  ring

/-- Exact PASS inequality for the one-scale resonance constant. -/
theorem QuarticFourSignedPolePair.threeTapResonancePaidCost_neg_iff_far_lt_neg_compensation
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapResonancePaidCost eps < 0
      ↔
    W.threeTapAdaptiveFarExact eps
      < - W.threeTapResonanceCompensation eps := by
  rw [W.threeTapResonancePaidCost_eq_far_add_compensation]
  linarith

/-- Exact FAIL-side weak inequality. -/
theorem QuarticFourSignedPolePair.threeTapResonancePaidCost_nonneg_iff_neg_compensation_le_far
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapResonancePaidCost eps
      ↔
    - W.threeTapResonanceCompensation eps
      <= W.threeTapAdaptiveFarExact eps := by
  rw [W.threeTapResonancePaidCost_eq_far_add_compensation]
  linarith

/-- Strict constant-term FAIL criterion. -/
theorem QuarticFourSignedPolePair.threeTapResonancePaidCost_pos_iff_neg_compensation_lt_far
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 < W.threeTapResonancePaidCost eps
      ↔
    - W.threeTapResonanceCompensation eps
      < W.threeTapAdaptiveFarExact eps := by
  rw [W.threeTapResonancePaidCost_eq_far_add_compensation]
  linarith

/-- Exact balanced-cost locus. -/
theorem QuarticFourSignedPolePair.threeTapResonancePaidCost_eq_zero_iff_far_eq_neg_compensation
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapResonancePaidCost eps = 0
      ↔
    W.threeTapAdaptiveFarExact eps
      = - W.threeTapResonanceCompensation eps := by
  rw [W.threeTapResonancePaidCost_eq_far_add_compensation]
  constructor <;> intro h <;> linarith

/-- Direct resonance PASS from the single remaining paid-cost comparison. -/
theorem QuarticFourSignedPolePair.exists_threeTapResonantTerminalProfile_pos_right_of_far_lt_neg_compensation
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hfar :
      W.threeTapAdaptiveFarExact eps
        < - W.threeTapResonanceCompensation eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        0 < W.threeTapAdaptiveTerminalProfile eps mult a := by
  apply W.exists_threeTapResonantTerminalProfile_pos_right_of_paidCost_neg
    ht hphase
  exact
    (W.threeTapResonancePaidCost_neg_iff_far_lt_neg_compensation).2 hfar

/-- Direct strict resonance FAIL from the opposite comparison. -/
theorem QuarticFourSignedPolePair.exists_threeTapResonantTerminalProfile_neg_right_of_neg_compensation_lt_far
    {t eps mult : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hphase : Real.cos (t * Real.log 2) = 0)
    (hfar :
      - W.threeTapResonanceCompensation eps
        < W.threeTapAdaptiveFarExact eps) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ a : ℝ, 0 < a → a < delta →
        W.threeTapAdaptiveTerminalProfile eps mult a < 0 := by
  apply W.exists_threeTapResonantTerminalProfile_neg_right_of_paidCost_pos
    ht hphase
  exact
    (W.threeTapResonancePaidCost_pos_iff_neg_compensation_lt_far).2 hfar

end Synthesis
