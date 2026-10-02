import Synthesis.RiemannSelectedPrimeSensitiveThreeTapAdaptiveTerminal

/-!
# Canonical capture of the adaptive-local transformed source

The adaptive local band has finite physical half-width
  r * eta_eps.
Choose once and for all a natural centered-window index strictly above that
half-width.  Every adaptive-local zero is contained in that window, so all
larger finite local sums stabilize exactly.

This removes the cutoff parameter from the transformed local budget and yields
a canonical local slack and terminal scalar.
-/

noncomputable section
namespace Synthesis

open MeasureTheory Set Filter
open scoped Real BigOperators

def QuarticFourSignedPolePair.threeTapAdaptiveCaptureIndex
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℕ :=
  Classical.choose
    (exists_nat_gt
      (quarticSignedPoleLocalHalfWidth
        t W.threeTapAdaptiveLocalRadius))

theorem QuarticFourSignedPolePair.threeTapAdaptiveCaptureIndex_gt
    {t : ℝ} (W : QuarticFourSignedPolePair t) :
    quarticSignedPoleLocalHalfWidth
        t W.threeTapAdaptiveLocalRadius
      < (W.threeTapAdaptiveCaptureIndex : ℝ) := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveCaptureIndex
  exact Classical.choose_spec
    (exists_nat_gt
      (quarticSignedPoleLocalHalfWidth
        t W.threeTapAdaptiveLocalRadius))

theorem QuarticFourSignedPolePair.threeTapAdaptiveLocal_mem_capture
    {t : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (hl : quarticSignedPoleThreeTapAdaptiveLocal W rho) :
    rho ∈ centeredZeroFinset t W.threeTapAdaptiveCaptureIndex := by
  have htpos : 0 < t := by linarith
  have heta : 0 <= W.threeTapAdaptiveLocalRadius :=
    W.threeTapAdaptiveLocalRadius_pos.le
  have hclosed :=
    (quarticSignedPoleLocal_iff_closed_ordinate_window
      htpos heta rho).mp hl
  have hN := W.threeTapAdaptiveCaptureIndex_gt
  rw [mem_centeredZeroFinset_iff]
  constructor <;> linarith

theorem QuarticFourSignedPolePair.threeTapAdaptiveLocalPairAt_stable
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {n : ℕ}
    (hn : W.threeTapAdaptiveCaptureIndex <= n) :
    W.threeTapAdaptiveLocalPairAt eps n
      =
    W.threeTapAdaptiveLocalPairAt eps W.threeTapAdaptiveCaptureIndex := by
  classical
  unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalPairAt
  apply Finset.sum_subset
  · exact centeredZeroFinset_mono hn
  · intro rho hrhon hrhoN
    by_cases hl : quarticSignedPoleThreeTapAdaptiveLocal W rho
    · exact False.elim
        (hrhoN (W.threeTapAdaptiveLocal_mem_capture ht hl))
    · simp [hl]

theorem QuarticFourSignedPolePair.threeTapAdaptiveLocalJetAt_stable
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {n : ℕ}
    (hn : W.threeTapAdaptiveCaptureIndex <= n) :
    W.threeTapAdaptiveLocalJetAt eps n
      =
    W.threeTapAdaptiveLocalJetAt eps W.threeTapAdaptiveCaptureIndex := by
  classical
  unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalJetAt
  apply Finset.sum_subset
  · exact centeredZeroFinset_mono hn
  · intro rho hrhon hrhoN
    by_cases hl : quarticSignedPoleThreeTapAdaptiveLocal W rho
    · exact False.elim
        (hrhoN (W.threeTapAdaptiveLocal_mem_capture ht hl))
    · simp [hl]

theorem QuarticFourSignedPolePair.threeTapAdaptiveLocalRemainderDebtAt_stable
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    {n : ℕ}
    (hn : W.threeTapAdaptiveCaptureIndex <= n) :
    W.threeTapAdaptiveLocalRemainderDebtAt eps n
      =
    W.threeTapAdaptiveLocalRemainderDebtAt
      eps W.threeTapAdaptiveCaptureIndex := by
  classical
  unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalRemainderDebtAt
  apply Finset.sum_subset
  · exact centeredZeroFinset_mono hn
  · intro rho hrhon hrhoN
    by_cases hl : quarticSignedPoleThreeTapAdaptiveLocal W rho
    · exact False.elim
        (hrhoN (W.threeTapAdaptiveLocal_mem_capture ht hl))
    · simp [hl]

def QuarticFourSignedPolePair.threeTapAdaptiveLocalExact
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.threeTapAdaptiveLocalExactAt eps W.threeTapAdaptiveCaptureIndex

def QuarticFourSignedPolePair.threeTapAdaptiveLocalBudget
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.threeTapAdaptiveLocalBudgetAt eps W.threeTapAdaptiveCaptureIndex

def QuarticFourSignedPolePair.threeTapAdaptiveLocalSlack
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.threeTapAdaptiveLocalBudget eps
    - W.threeTapAdaptiveLocalExact eps

theorem QuarticFourSignedPolePair.threeTapAdaptiveLocalExact_le_budget
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapAdaptiveLocalExact eps
      <= W.threeTapAdaptiveLocalBudget eps := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalExact
    QuarticFourSignedPolePair.threeTapAdaptiveLocalBudget
  exact W.threeTapAdaptiveLocalExactAt_le_budget
    W.threeTapAdaptiveCaptureIndex

theorem QuarticFourSignedPolePair.threeTapAdaptiveLocalSlack_nonneg
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.threeTapAdaptiveLocalSlack eps := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalSlack
  exact sub_nonneg.mpr W.threeTapAdaptiveLocalExact_le_budget

theorem QuarticFourSignedPolePair.threeTapAdaptiveLocalExactAt_eventually_eq
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    ∀ᶠ n : ℕ in atTop,
      W.threeTapAdaptiveLocalExactAt eps n
        = W.threeTapAdaptiveLocalExact eps := by
  refine eventually_atTop.2
    ⟨W.threeTapAdaptiveCaptureIndex, ?_⟩
  intro n hn
  unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalExact
    QuarticFourSignedPolePair.threeTapAdaptiveLocalExactAt
  rw [W.threeTapAdaptiveLocalPairAt_stable ht hn]

theorem QuarticFourSignedPolePair.threeTapAdaptiveLocalBudgetAt_eventually_eq
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    ∀ᶠ n : ℕ in atTop,
      W.threeTapAdaptiveLocalBudgetAt eps n
        = W.threeTapAdaptiveLocalBudget eps := by
  refine eventually_atTop.2
    ⟨W.threeTapAdaptiveCaptureIndex, ?_⟩
  intro n hn
  unfold QuarticFourSignedPolePair.threeTapAdaptiveLocalBudget
    QuarticFourSignedPolePair.threeTapAdaptiveLocalBudgetAt
  rw [W.threeTapAdaptiveLocalJetAt_stable ht hn,
      W.threeTapAdaptiveLocalRemainderDebtAt_stable ht hn]

def QuarticFourSignedPolePair.threeTapAdaptiveFarExact
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
    - W.threeTapAdaptiveLocalExact eps

theorem QuarticFourSignedPolePair.threeTap_offOrd_eq_local_add_far
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
      =
    W.threeTapAdaptiveLocalExact eps
      + W.threeTapAdaptiveFarExact eps := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveFarExact
  ring

def QuarticFourSignedPolePair.threeTapAdaptiveTerminalMargin
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) (rho : Zeros) : ℝ :=
  W.threeTapSelectedTerminalMargin eps rho
    (W.threeTapAdaptiveLocalSlack eps)

theorem QuarticFourSignedPolePair.threeTapAdaptiveTerminalMargin_eq_eventual_finite
    {t eps : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    ∀ᶠ n : ℕ in atTop,
      W.threeTapAdaptiveTerminalMarginAt eps rho n
        = W.threeTapAdaptiveTerminalMargin eps rho := by
  filter_upwards
    [W.threeTapAdaptiveLocalExactAt_eventually_eq ht (eps:=eps),
     W.threeTapAdaptiveLocalBudgetAt_eventually_eq ht (eps:=eps)]
    with n hex hbud
  unfold QuarticFourSignedPolePair.threeTapAdaptiveTerminalMarginAt
    QuarticFourSignedPolePair.threeTapAdaptiveTerminalMargin
    QuarticFourSignedPolePair.threeTapAdaptiveLocalSlackAt
    QuarticFourSignedPolePair.threeTapAdaptiveLocalSlack
  rw [hex,hbud]

theorem QuarticFourSignedPolePair.threeTapAdaptiveTerminalMargin_sub_canonical
    {t eps EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.threeTapAdaptiveTerminalMargin eps rho
      - W.canonicalTerminalMargin rho EV
    =
    2*eps * W.threeTapCombinedTargetLinearCoeff rho
      + 2*eps^2 * W.threeTapCombinedTargetQuadraticCoeff rho
      - (W.threeTapCompletedExternal eps - W.completedSignedResidual)
      - (1/2 : ℝ) *
          (W.threeTapAdaptiveLocalSlack eps
            - W.canonicalLocalBudgetSlack EV) := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveTerminalMargin
  exact W.threeTapSelectedTerminalMargin_sub_canonical ht rho

theorem QuarticFourSignedPolePair.threeTapAdaptiveTerminalMargin_sub_canonical_at_resonance
    {t eps EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hphase : Real.cos (t * Real.log 2) = 0) :
    W.threeTapAdaptiveTerminalMargin eps rho
      - W.canonicalTerminalMargin rho EV
    =
    2*eps * W.threeTapCombinedTargetLinearCoeff rho
      + 2*eps^2 * W.threeTapCombinedTargetQuadraticCoeff rho
      -
      (
        W.threeTapChannelCombination eps
          Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.offOrdProjectiveDefect
        + W.threeTapChannelCombination eps
          Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect
        + W.threeTapChannelCombination eps
          Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect
        - W.completedSignedResidual
      )
      - (1/2 : ℝ) *
          (W.threeTapAdaptiveLocalSlack eps
            - W.canonicalLocalBudgetSlack EV) := by
  unfold QuarticFourSignedPolePair.threeTapAdaptiveTerminalMargin
  exact
    W.threeTapSelectedTerminalMargin_sub_canonical_at_resonance
      ht rho hphase

end Synthesis
