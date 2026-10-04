import Synthesis.RiemannSelectedPrimeSensitiveThreeTapFiniteAsymptotic
import Synthesis.RiemannSelectedPrimeSensitiveThreeTapPaidCostCut

/-!
# Exact local-compensation floor

The split Route-A compiler uses a lower bound

  H <= LocalExact - Compensation.

This quantity has a simpler exact form.  Since

  LocalSlack = LocalBudget - LocalExact,

we have

  LocalExact - Compensation
    = -(Gamma + Pole) - 1/2 LocalSlack.

Thus the compensation floor is controlled by two already meaningful objects:
a negative completed gamma+pole channel and the nonnegative paid local slack.
No sign of the translated pole channel is inserted here.
-/

noncomputable section
namespace Synthesis

open scoped Real

/-- Completed gamma plus finite-pole part of the translated channel. -/
def QuarticFourSignedPolePair.threeTapGammaPoleCombination
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (eps : ℝ) : ℝ :=
  W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.gammaProjectiveDefect
    +
  W.threeTapChannelCombination eps
      Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition.poleProjectiveDefect

/-- Exact algebraic normal form for the Route-A compensation threshold. -/
theorem QuarticFourSignedPolePair.threeTapLocalMinusCompensation_eq
    {t eps : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.threeTapAdaptiveLocalExact eps
        - W.threeTapResonanceCompensation eps
      =
    - W.threeTapGammaPoleCombination eps
      - (1/2 : ℝ) * W.threeTapAdaptiveLocalSlack eps := by
  unfold QuarticFourSignedPolePair.threeTapResonanceCompensation
    QuarticFourSignedPolePair.threeTapGammaPoleCombination
    QuarticFourSignedPolePair.threeTapAdaptiveLocalSlack
  ring

/-- A negative gamma+pole gain G and a local-slack upper bound S give the
explicit lower floor G-S/2. -/
theorem QuarticFourSignedPolePair.threeTapLocalMinusCompensation_ge_of_gammaPole_slack
    {t eps G S : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hgp : W.threeTapGammaPoleCombination eps <= -G)
    (hslack : W.threeTapAdaptiveLocalSlack eps <= S) :
    G - (1/2 : ℝ)*S
      <= W.threeTapAdaptiveLocalExact eps
          - W.threeTapResonanceCompensation eps := by
  rw [W.threeTapLocalMinusCompensation_eq]
  linarith

/-- Positive-floor form convenient for the split PASS compiler. -/
theorem QuarticFourSignedPolePair.threeTapPositiveCompensationFloor_of_gammaPole_slack
    {t eps G S H : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hgp : W.threeTapGammaPoleCombination eps <= -G)
    (hslack : W.threeTapAdaptiveLocalSlack eps <= S)
    (hH : H <= G - (1/2 : ℝ)*S) :
    H <= W.threeTapAdaptiveLocalExact eps
        - W.threeTapResonanceCompensation eps := by
  exact hH.trans
    (W.threeTapLocalMinusCompensation_ge_of_gammaPole_slack hgp hslack)

/-- Route-A PASS with the compensation input split into gamma+pole gain and
local-slack debt.  M0 is already discharged by the uniform finite theorem. -/
theorem QuarticFourSignedPolePair.exists_threeTapGammaPoleSlackPass_constants :
    ∃ C Cmu : ℝ, 0 <= C ∧ 0 <= Cmu ∧
      ∀ {t eps G S H : ℝ},
        200 <= t ->
        ∀ W : QuarticFourSignedPolePair t,
        threeTapUniformFiniteHalfHeightBudget t eps C Cmu <= H ->
        W.threeTapPairAdverseFarAfter eps (t/2) < H ->
        W.threeTapGammaPoleCombination eps <= -G ->
        W.threeTapAdaptiveLocalSlack eps <= S ->
        H <= G - (1/2 : ℝ)*S ->
        W.threeTapResonancePaidCost eps < 0 := by
  obtain ⟨C,Cmu,hC,hCmu,hpass⟩ :=
    QuarticFourSignedPolePair.exists_threeTapHalfHeightUniformFinitePass_constants
  refine ⟨C,Cmu,hC,hCmu,?_⟩
  intro t eps G S H ht W hfinite hfar hgp hslack hH
  apply hpass ht W hfinite hfar
  exact W.threeTapPositiveCompensationFloor_of_gammaPole_slack hgp hslack hH

end Synthesis
