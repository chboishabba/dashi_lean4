import Synthesis.RiemannProjectiveQuarticFourWindowSignedPolePostSixthAbsorb

/-!
# A2 strict-ABSORB scalar audit

The post-sixth route is no longer blocked on orientation.  This file performs
one analytic normalization of the live terminal scalar and then stops: no new
terminal wrapper and no replacement carrier is introduced.

The local selected-M6 budget is written exactly as

  positive/local debt - smooth-mu gain,

with the signed FarExact coordinate kept outside that local split.  This makes
the remaining A2 inequality read literally

  localDebt + FarExact < compensationTargetThreshold + muGain.

The selected terminal M6 certificate already beats the dominant quartic-vs-
sixth coefficient at the canonical radius.  We expose that fact on the same
selected witness, so any remaining failure of A2 is necessarily in the lower-
order/local-count, eighth-order, far, or compensation coordinates rather than
in the dominant sixth coefficient.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real BigOperators

namespace Synthesis

/-- All non-favorable local coordinates of the selected-M6 terminal budget.
The favorable smooth-mu term is deliberately excluded. -/
def QuarticFourSignedPolePair.postSixthTerminalLocalPositiveDebt
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (EV : ℝ) : ℝ :=
  let eta := quarticSignedPoleCanonicalLocalRadius
  let r := quarticSignedPoleLocalHalfWidth t eta
  let NZ : ℝ :=
    (zetaZeroConfig.N (t-r-1) (t+r) : ℝ)
  (W.targetStrength / (6 * (t/16)^6))
      * (EV + (3/2 : ℝ) * r^2 * NZ)
    +
  (((3/20 : ℝ) * Real.pi^6)
      * quarticSignedPoleLocalSixthPhaseEnvelope t eta
      / (720 * (t/16)^8)) * NZ
    +
  (((Real.pi+1)^2 * W.fourthLipschitz)
      * quarticSignedPoleLocalEighthPhysicalEnvelope t eta
      / (t/16)^10) * NZ

/-- The favorable smooth density contribution in the selected-M6 terminal
budget. -/
def QuarticFourSignedPolePair.postSixthTerminalLocalMuGain
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  let eta := quarticSignedPoleCanonicalLocalRadius
  let r := quarticSignedPoleLocalHalfWidth t eta
  (W.targetStrength / (6 * (t/16)^6))
    * ((2/5 : ℝ) * r^5
      * quarticSignedPoleMuLowerEnvelope (t-r))

/-- Exact A2 local normal form. -/
theorem QuarticFourSignedPolePair.postSixthTerminalLocalM6Budget_eq_debt_sub_muGain
    {t EV : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.postSixthTerminalLocalM6Budget EV
      = W.postSixthTerminalLocalPositiveDebt EV
        - W.postSixthTerminalLocalMuGain := by
  unfold QuarticFourSignedPolePair.postSixthTerminalLocalM6Budget
    QuarticFourSignedPolePair.postSixthTerminalLocalPositiveDebt
    QuarticFourSignedPolePair.postSixthTerminalLocalMuGain
  dsimp
  ring

/-- Exact finite A2 normal form, retaining FarExact signed. -/
theorem QuarticFourSignedPolePair.postSixthTerminalM6BudgetAt_eq_debt_sub_muGain_add_far
    {t EV : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.postSixthTerminalM6BudgetAt EV n
      = W.postSixthTerminalLocalPositiveDebt EV
        - W.postSixthTerminalLocalMuGain
        + W.literalFarExactAt quarticSignedPoleCanonicalLocalRadius n := by
  rw [W.postSixthTerminalM6BudgetAt_eq_local_add_far]
  rw [W.postSixthTerminalLocalM6Budget_eq_debt_sub_muGain]
  ring

/-- The strict A2 scalar is exactly a gain-versus-debt comparison.  No
absolute value is introduced on FarExact. -/
theorem QuarticFourSignedPolePair.postSixthTerminalM6BudgetAt_lt_threshold_iff
    {t EV : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (n : ℕ) :
    W.postSixthTerminalM6BudgetAt EV n
        < W.compensationTargetThreshold rho
      ↔
    W.postSixthTerminalLocalPositiveDebt EV
        + W.literalFarExactAt quarticSignedPoleCanonicalLocalRadius n
      < W.compensationTargetThreshold rho
        + W.postSixthTerminalLocalMuGain := by
  rw [W.postSixthTerminalM6BudgetAt_eq_debt_sub_muGain_add_far]
  constructor <;> intro h <;> linarith

/-- At high height the canonical physical half-width is at most `t/64`. -/
theorem quarticSignedPoleCanonicalLocalHalfWidth_le_t_div_64
    {t : ℝ} (ht : 0 <= t) :
    quarticSignedPoleLocalHalfWidth
        t quarticSignedPoleCanonicalLocalRadius
      <= t/64 := by
  have hden : 0 < Real.pi + 1 := by positivity
  have heta :
      quarticSignedPoleCanonicalLocalRadius <= (1/4 : ℝ) := by
    unfold quarticSignedPoleCanonicalLocalRadius
    rw [div_le_iff₀ hden]
    nlinarith [Real.pi_gt_three]
  have ht16 : 0 <= t/16 := by positivity
  unfold quarticSignedPoleLocalHalfWidth
  calc
    quarticSignedPoleCanonicalLocalRadius * (t/16)
      <= (1/4 : ℝ) * (t/16) :=
        mul_le_mul_of_nonneg_right heta ht16
    _ = t/64 := by ring

/-- The explicit Stirling lower envelope used by A2 is genuinely favorable on
the entire high-height range. -/
theorem quarticSignedPoleMuLowerEnvelope_canonical_pos
    {t : ℝ} (ht : 200 <= t) :
    0 < quarticSignedPoleMuLowerEnvelope
      (t - quarticSignedPoleLocalHalfWidth
        t quarticSignedPoleCanonicalLocalRadius) := by
  let r := quarticSignedPoleLocalHalfWidth
    t quarticSignedPoleCanonicalLocalRadius
  let T := t-r
  have hr : r <= t/64 := by
    dsimp [r]
    exact quarticSignedPoleCanonicalLocalHalfWidth_le_t_div_64
      (by linarith)
  have hT : 100 < T := by
    dsimp [T]
    linarith
  have hTpos : 0 < T := by linarith
  have hT2 : 0 < T^2 := by positivity
  have hpi4 : Real.pi < 4 := Real.pi_lt_four
  have hratio : (2 : ℝ) <= T / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity : 0 < 2 * Real.pi)]
    nlinarith
  have hlog2 : (1/2 : ℝ) <= Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos
      (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hlog :
      (1/2 : ℝ) <= Real.log (T / (2 * Real.pi)) := by
    exact hlog2.trans
      (Real.log_le_log (by norm_num) hratio)
  have herr : 20 / T^2 < (1/2 : ℝ) := by
    rw [div_lt_iff₀ hT2]
    nlinarith
  have hcore :
      20 / T^2 < Real.log (T / (2 * Real.pi)) :=
    herr.trans_le hlog
  have hfac : 0 < 1 / (2 * Real.pi) := by positivity
  dsimp [T, r] at hcore ⊢
  unfold quarticSignedPoleMuLowerEnvelope
  rw [show
      (20 / (2 * Real.pi)) /
          (t - quarticSignedPoleLocalHalfWidth
            t quarticSignedPoleCanonicalLocalRadius)^2
        =
      (1 / (2 * Real.pi))
        * (20 /
          (t - quarticSignedPoleLocalHalfWidth
            t quarticSignedPoleCanonicalLocalRadius)^2) by ring]
  exact sub_pos.mpr (mul_lt_mul_of_pos_left hcore hfac)

/-- Consequently the smooth-mu coordinate in the A2 split is strictly
favorable for every live witness at `t >= 200`. -/
theorem QuarticFourSignedPolePair.postSixthTerminalLocalMuGain_pos
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    0 < W.postSixthTerminalLocalMuGain := by
  have ht0 : 0 < t := by linarith
  have heta : 0 < quarticSignedPoleCanonicalLocalRadius :=
    quarticSignedPoleCanonicalLocalRadius_pos
  have hr :
      0 < quarticSignedPoleLocalHalfWidth
        t quarticSignedPoleCanonicalLocalRadius := by
    unfold quarticSignedPoleLocalHalfWidth
    positivity
  have hmu := quarticSignedPoleMuLowerEnvelope_canonical_pos ht
  unfold QuarticFourSignedPolePair.postSixthTerminalLocalMuGain
  dsimp
  positivity

/-- Name the selected-M6 dominant allowance already certified in the source. -/
def quarticSignedPoleTerminalM6DominantAllowance : ℝ :=
  (1/24 : ℝ)
    * ((3/20 : ℝ) * Real.pi^6)
    * quarticSignedPoleCanonicalLocalRadius^2

theorem quarticSignedPoleTerminalM6DominantAllowance_lt_strengthFloor :
    quarticSignedPoleTerminalM6DominantAllowance
      < quarticSignedPoleStrengthFloor := by
  exact quarticSignedPole_terminal_M6_cap_pays_dominant_balance

/-- Any floor-certified witness therefore has a strict positive dominant A2
coefficient. -/
theorem QuarticFourSignedPolePair.terminalM6DominantAllowance_lt_targetStrength
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hfloor : quarticSignedPoleStrengthFloor <= W.targetStrength) :
    quarticSignedPoleTerminalM6DominantAllowance < W.targetStrength :=
  quarticSignedPoleTerminalM6DominantAllowance_lt_strengthFloor.trans_le hfloor

/-- The same selected witness simultaneously owns the target floor, the
terminal M6 interval, its negative sign, and the favorable dominant
coefficient.  Thus the leading A2 sign is paid rather than hypothetical. -/
theorem exists_quarticFourSignedPolePair_with_terminal_M6_and_dominant_A2_sign
    {t : ℝ} (ht : 200 <= t) :
    ∃ W : QuarticFourSignedPolePair t,
      quarticSignedPoleStrengthFloor <= W.targetStrength
        ∧
      -(3/20 : ℝ) * Real.pi^6 <= W.signedProfileMomentSix
        ∧
      W.signedProfileMomentSix < 0
        ∧
      quarticSignedPoleTerminalM6DominantAllowance < W.targetStrength := by
  obtain ⟨W,hfloor,hM6lo,hM6neg⟩ :=
    exists_quarticFourSignedPolePair_with_strength_floor_and_terminal_M6 ht
  refine ⟨W, ?_, hM6lo, hM6neg, ?_⟩
  · simpa [quarticSignedPoleStrengthFloor] using hfloor
  · exact W.terminalM6DominantAllowance_lt_targetStrength
      (by simpa [quarticSignedPoleStrengthFloor] using hfloor)

end Synthesis
