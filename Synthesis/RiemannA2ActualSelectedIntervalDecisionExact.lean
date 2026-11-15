import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleA2ScalarAudit
import Mathlib.Tactic

/-!
RH A2: ORIGINAL SAME-WITNESS, SAME-ZERO, SAME-CUTOFF interval compiler.

Unlike the proposed bare inverse-square curvature or artificial heat
spectrum, every scalar here is a literal field or existing original
definition on QuarticFourSignedPolePair, Zeros, the original finite
centeredZeroFinset and the original Stirling-mu target.

This is a sound conditional analytic producer: finite actual-source
intervals can decide PASS or NO-GO, and a cofinal uniform reverse
bound gives a genuine source-typed eventual no-go. No local/far,
compensation or actual-zero bounds are supplied in this module.
SOURCE-WRITTEN; pinned Lean 4.28 kernel acceptance still required.
-/

noncomputable section
namespace Synthesis

/-- Decision boundary in literal original A2 coordinates. -/
def QuarticFourSignedPolePair.selectedA2LiteralGap
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (EV : ℝ) (n : ℕ) : ℝ :=
  W.compensationTargetThreshold rho
    + W.postSixthTerminalLocalMuGain
    - W.postSixthTerminalLocalPositiveDebt EV
    - W.literalFarExactAt quarticSignedPoleCanonicalLocalRadius n

/-- Source exact strict A2 is positivity of this signed gap, with
no new absolute-value allowance for FarExact. -/
theorem QuarticFourSignedPolePair.selectedA2LiteralGap_pos_iff
    {t EV : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (n : ℕ) :
    0 < W.selectedA2LiteralGap rho EV n ↔
      W.postSixthTerminalM6BudgetAt EV n <
        W.compensationTargetThreshold rho := by
  rw [W.postSixthTerminalM6BudgetAt_lt_threshold_iff rho n]
  unfold QuarticFourSignedPolePair.selectedA2LiteralGap
  constructor <;> intro h <;> linarith

/-- Rigorous interval PASS. Every bound explicitly controls its
source-real scalar on exactly the same W,rho,EV,n. -/
theorem QuarticFourSignedPolePair.selectedA2Pass_of_source_intervals
    {t EV : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (n : ℕ)
    (debtHi farHi compLo muLo : ℝ)
    (hd : W.postSixthTerminalLocalPositiveDebt EV ≤ debtHi)
    (hf : W.literalFarExactAt quarticSignedPoleCanonicalLocalRadius n ≤ farHi)
    (hc : compLo ≤ W.compensationTargetThreshold rho)
    (hm : muLo ≤ W.postSixthTerminalLocalMuGain)
    (hgap : debtHi + farHi < compLo + muLo) :
    W.postSixthTerminalM6BudgetAt EV n <
      W.compensationTargetThreshold rho := by
  apply (W.postSixthTerminalM6BudgetAt_lt_threshold_iff rho n).2
  linarith

/-- Rigorous interval NO-GO for the selected actual finite A2 scalar.
This is NOT an unconditional theorem about its true zeta-zero input. -/
theorem QuarticFourSignedPolePair.selectedA2NoGo_of_source_intervals
    {t EV : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (n : ℕ)
    (debtLo farLo compHi muHi : ℝ)
    (hd : debtLo ≤ W.postSixthTerminalLocalPositiveDebt EV)
    (hf : farLo ≤
      W.literalFarExactAt quarticSignedPoleCanonicalLocalRadius n)
    (hc : W.compensationTargetThreshold rho ≤ compHi)
    (hm : W.postSixthTerminalLocalMuGain ≤ muHi)
    (hgap : compHi + muHi ≤ debtLo + farLo) :
    ¬ W.postSixthTerminalM6BudgetAt EV n <
      W.compensationTargetThreshold rho := by
  intro hpass
  have h := (W.postSixthTerminalM6BudgetAt_lt_threshold_iff rho n).1 hpass
  linarith

/-- A TRUE cofinal source interval reverse estimate (if analytically
constructed) yields a TRUE eventually-failed original A2 scalar.
Nothing about hypothetical free zero placements is assumed. -/
theorem QuarticFourSignedPolePair.selectedA2CofinalNoGo_of_source_intervals
    {t EV : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) (N : ℕ)
    (debtLo farLo compHi muHi : ℝ)
    (hd : debtLo ≤ W.postSixthTerminalLocalPositiveDebt EV)
    (hf : ∀ n ≥ N, farLo ≤
      W.literalFarExactAt quarticSignedPoleCanonicalLocalRadius n)
    (hc : W.compensationTargetThreshold rho ≤ compHi)
    (hm : W.postSixthTerminalLocalMuGain ≤ muHi)
    (hgap : compHi + muHi ≤ debtLo + farLo) :
    ∀ n ≥ N, ¬ W.postSixthTerminalM6BudgetAt EV n <
      W.compensationTargetThreshold rho := by
  intro n hn
  exact W.selectedA2NoGo_of_source_intervals rho n
    debtLo farLo compHi muHi hd (hf n hn) hc hm hgap

end Synthesis
