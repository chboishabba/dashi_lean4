import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleFourierMass

/-!
# Clay-facing quartic signed-pole Fourier recut

The previous terminal interface hid the smooth background inside

  integral Psi_t(x) * mu(x) dx.

The Fourier-mass weld now splits that same object exactly into

  128*pi*mu(t)/(t*R*M0) * OriginDet_W
    + fullMuVariation_W.

This file changes no mathematics in the contradiction compiler.  It only
re-expresses the remaining ordinary analytic theorem on the exact coordinates
that must cancel:

  canonical literal far zero source
  - explicit constant-density origin mode
  - full mu-variation.

Thus there is no remaining representation debt between the proposed analytic
estimate below and the existing above-Platt--Trudgian RH contradiction
compiler.
-/

noncomputable section

open MeasureTheory Set
open scoped Real

namespace Synthesis

def LiteralFarExplicitOriginVariationUniformHighEstimate
    (CV T : ℝ) : Prop :=
  ∀ {t : ℝ},
    T < t ->
    ∀ {rho : Zeros},
      (rho : ℂ).im = t ->
      heightOf rho ≠ 0 ->
      ∃ W : QuarticFourSignedPolePair t,
        quarticSignedPoleStrengthFloor <= W.targetStrength
          ∧
        -(3/20 : ℝ) * Real.pi^6 <= W.signedProfileMomentSix
          ∧
        W.signedProfileMomentSix < 0
          ∧
        8/t < W.quantitativeTargetRadius
          ∧
        (1/2 : ℝ)
          *
          (
            W.canonicalLiteralFarPairSource
            -
            (128 * Real.pi * Zeta23.mu t
                / (t * W.R * unitBumpMass0))
              *
            quarticFourSmoothFinitePoleCancelledOrigin
                W.R W.muHalf W.muTwo t
            -
            W.fullMuVariation
          )
          <
        W.postSixthTerminalResidualMargin rho
          (quarticSignedPoleCanonicalV4Error CV t)

theorem literalFarExplicitOriginVariationUniformHighEstimate_iff_old
    {CV T : ℝ}
    (hPT : quarticPlattTrudgianCutoff <= T) :
    LiteralFarExplicitOriginVariationUniformHighEstimate CV T
      ↔
    LiteralFarMinusMuUniformHighEstimate CV T := by
  constructor
  · intro hnew t ht rho him hoff
    obtain ⟨W,hS,hM6lo,hM6neg,hband,hcut⟩ :=
      hnew ht him hoff
    have ht0 : 0 < t := by
      have hPT200 := quarticPlattTrudgianCutoff_gt_twoHundred
      have hPTt : quarticPlattTrudgianCutoff < t :=
        lt_of_le_of_lt hPT ht
      linarith
    refine ⟨W,hS,hM6lo,hM6neg,hband,?_⟩
    rw [W.fullMuIntegral_eq_centerDensity_add_variation ht0]
    rw [W.centerDensityMode_eq_originDet ht0]
    exact hcut
  · intro hold t ht rho him hoff
    obtain ⟨W,hS,hM6lo,hM6neg,hband,hcut⟩ :=
      hold ht him hoff
    have ht0 : 0 < t := by
      have hPT200 := quarticPlattTrudgianCutoff_gt_twoHundred
      have hPTt : quarticPlattTrudgianCutoff < t :=
        lt_of_le_of_lt hPT ht
      linarith
    refine ⟨W,hS,hM6lo,hM6neg,hband,?_⟩
    rw [← W.centerDensityMode_eq_originDet ht0]
    rw [← W.fullMuIntegral_eq_centerDensity_add_variation ht0]
    exact hcut

theorem exists_quarticSignedPoleFixedHigh_explicitOriginVariationEstimate_excludes_offLine :
    ∃ CV T : ℝ,
      0 <= CV
        ∧ quarticPlattTrudgianCutoff <= T
        ∧
      (
        LiteralFarExplicitOriginVariationUniformHighEstimate CV T
        ->
        ∀ {t : ℝ},
          T < t ->
          ∀ {rho : Zeros},
            (rho : ℂ).im = t ->
            heightOf rho ≠ 0 ->
            False
      ) := by
  obtain ⟨CV,T,hCV,hPT,hexclude⟩ :=
    exists_quarticSignedPoleFixedHigh_uniformLiteralFarMinusMuEstimate_excludes_offLine
  refine ⟨CV,T,hCV,hPT,?_⟩
  intro hnew
  exact hexclude
    ((literalFarExplicitOriginVariationUniformHighEstimate_iff_old hPT).1 hnew)

theorem exists_quarticSignedPoleFixedHigh_offLine_forces_explicitOriginVariationEstimate_failure :
    ∃ CV T : ℝ,
      0 <= CV
        ∧ quarticPlattTrudgianCutoff <= T
        ∧
      (
        (∃ t : ℝ, T < t ∧
          ∃ rho : Zeros,
            (rho : ℂ).im = t ∧ heightOf rho ≠ 0)
        ->
        ¬ LiteralFarExplicitOriginVariationUniformHighEstimate CV T
      ) := by
  obtain ⟨CV,T,hCV,hPT,hexclude⟩ :=
    exists_quarticSignedPoleFixedHigh_explicitOriginVariationEstimate_excludes_offLine
  refine ⟨CV,T,hCV,hPT,?_⟩
  rintro ⟨t,ht,rho,him,hoff⟩ hnew
  exact hexclude hnew ht him hoff


/-!
## Local-budget slack normal form

The canonical high residual has a simpler exact form than either the literal
far-minus-mu or the Fourier center-density presentation:

  H_W = completedSignedResidual - 1/2 * canonicalLiteralLocalExact.

The terminal margin is

  2*heightDefect - 1/2*postSixthTerminalLocalM6Budget.

Hence the terminal inequality is exactly equivalent to

  completedSignedResidual
    + 1/2 * (postSixthTerminalLocalM6Budget
             - canonicalLiteralLocalExact)
  < 2*heightDefect.

The parenthesized quantity is the already-paid local upper-bound slack.
This isolates all genuinely global analytic debt in completedSignedResidual.
-/

theorem QuarticFourSignedPolePair.canonicalSignedHighResidual_eq_completed_sub_localHalf
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.canonicalSignedHighResidual
      =
    W.completedSignedResidual
      - (1/2 : ℝ) * W.canonicalLiteralLocalExact := by
  unfold QuarticFourSignedPolePair.canonicalSignedHighResidual
    QuarticFourSignedPolePair.canonicalLiteralVsPairedLocalCorrection
  rw [W.canonicalFarBoundaryCoupledCompensation_eq_completed_sub_localPaired ht]
  ring

def QuarticFourSignedPolePair.canonicalLocalBudgetSlack
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (EV : ℝ) : ℝ :=
  W.postSixthTerminalLocalM6Budget EV
    - W.canonicalLiteralLocalExact

theorem QuarticFourSignedPolePair.postSixthCanonicalSignedHighCut_iff_completed_plus_localSlack
    {t EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.PostSixthCanonicalSignedHighCut rho EV
      ↔
    W.completedSignedResidual
        + (1/2 : ℝ) * W.canonicalLocalBudgetSlack EV
      <
    2 * W.combinedZeroHeightDefect rho := by
  unfold QuarticFourSignedPolePair.PostSixthCanonicalSignedHighCut
    QuarticFourSignedPolePair.postSixthTerminalResidualMargin
    QuarticFourSignedPolePair.canonicalLocalBudgetSlack
  rw [W.canonicalSignedHighResidual_eq_completed_sub_localHalf
    (by linarith : 0 < t)]
  constructor <;> intro h <;> linarith

theorem QuarticFourSignedPolePair.canonicalLocalBudgetSlack_nonneg
    {t EV : ℝ}
    (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hM6lo :
      -(3/20 : ℝ) * Real.pi^6 <= W.signedProfileMomentSix)
    (hM6neg : W.signedProfileMomentSix < 0)
    (hV :
      |quarticSignedPoleRvMVerticalFourthDiscrepancy
        t
        (quarticSignedPoleLocalHalfWidth
          t quarticSignedPoleCanonicalLocalRadius)|
        <= EV) :
    0 <= W.canonicalLocalBudgetSlack EV := by
  let n := quarticSignedPoleCanonicalLocalExhaustionIndex t
  have hn :
      quarticSignedPoleCanonicalPhysicalHalfWidth t < (n : ℝ) := by
    dsimp [n]
    exact quarticSignedPoleCanonicalLocalExhaustionIndex_spec t
  have hlocal :=
    W.literalLocalExactAt_le_postSixthTerminalLocalM6Budget
      ht hM6lo hM6neg n hn hV
  have hstab :=
    W.literalLocalExactAt_eq_canonical
      (by linarith : 0 < t) n hn
  rw [hstab] at hlocal
  unfold QuarticFourSignedPolePair.canonicalLocalBudgetSlack
  linarith

def CompletedResidualWithLocalSlackUniformHighEstimate
    (CV T : ℝ) : Prop :=
  ∀ {t : ℝ},
    T < t ->
    ∀ {rho : Zeros},
      (rho : ℂ).im = t ->
      heightOf rho ≠ 0 ->
      ∃ W : QuarticFourSignedPolePair t,
        quarticSignedPoleStrengthFloor <= W.targetStrength
          ∧
        -(3/20 : ℝ) * Real.pi^6 <= W.signedProfileMomentSix
          ∧
        W.signedProfileMomentSix < 0
          ∧
        8/t < W.quantitativeTargetRadius
          ∧
        W.completedSignedResidual
            + (1/2 : ℝ) *
              W.canonicalLocalBudgetSlack
                (quarticSignedPoleCanonicalV4Error CV t)
          <
        2 * W.combinedZeroHeightDefect rho

theorem completedResidualWithLocalSlackUniformHighEstimate_iff_literalFar
    {CV T : ℝ}
    (hPT : quarticPlattTrudgianCutoff <= T) :
    CompletedResidualWithLocalSlackUniformHighEstimate CV T
      ↔
    LiteralFarMinusMuUniformHighEstimate CV T := by
  constructor
  · intro hnew t ht rho him hoff
    obtain ⟨W,hS,hM6lo,hM6neg,hband,hcut⟩ :=
      hnew ht him hoff
    have ht200 : 200 <= t := by
      have hPT200 := quarticPlattTrudgianCutoff_gt_twoHundred
      have hPTt : quarticPlattTrudgianCutoff < t :=
        lt_of_le_of_lt hPT ht
      linarith
    refine ⟨W,hS,hM6lo,hM6neg,hband,?_⟩
    have hcanon :
        W.PostSixthCanonicalSignedHighCut rho
          (quarticSignedPoleCanonicalV4Error CV t) :=
      (W.postSixthCanonicalSignedHighCut_iff_completed_plus_localSlack
        ht200 rho).2 hcut
    exact
      (W.postSixthCanonicalSignedHighCut_iff_literalFar
        ht200 rho).1 hcanon
  · intro hold t ht rho him hoff
    obtain ⟨W,hS,hM6lo,hM6neg,hband,hcut⟩ :=
      hold ht him hoff
    have ht200 : 200 <= t := by
      have hPT200 := quarticPlattTrudgianCutoff_gt_twoHundred
      have hPTt : quarticPlattTrudgianCutoff < t :=
        lt_of_le_of_lt hPT ht
      linarith
    refine ⟨W,hS,hM6lo,hM6neg,hband,?_⟩
    have hcanon :
        W.PostSixthCanonicalSignedHighCut rho
          (quarticSignedPoleCanonicalV4Error CV t) :=
      (W.postSixthCanonicalSignedHighCut_iff_literalFar
        ht200 rho).2 hcut
    exact
      (W.postSixthCanonicalSignedHighCut_iff_completed_plus_localSlack
        ht200 rho).1 hcanon

theorem exists_quarticSignedPoleFixedHigh_completedResidualWithLocalSlack_excludes_offLine :
    ∃ CV T : ℝ,
      0 <= CV
        ∧ quarticPlattTrudgianCutoff <= T
        ∧
      (
        CompletedResidualWithLocalSlackUniformHighEstimate CV T
        ->
        ∀ {t : ℝ},
          T < t ->
          ∀ {rho : Zeros},
            (rho : ℂ).im = t ->
            heightOf rho ≠ 0 ->
            False
      ) := by
  obtain ⟨CV,T,hCV,hPT,hexclude⟩ :=
    exists_quarticSignedPoleFixedHigh_uniformLiteralFarMinusMuEstimate_excludes_offLine
  refine ⟨CV,T,hCV,hPT,?_⟩
  intro hnew
  exact hexclude
    ((completedResidualWithLocalSlackUniformHighEstimate_iff_literalFar hPT).1 hnew)

end Synthesis
