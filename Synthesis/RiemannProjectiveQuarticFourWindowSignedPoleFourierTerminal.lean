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


/-!
## Exact quartic-scale paired Abel normalization

Let r=t/16.  The existing pointwise theorem gives, for q >= 0,

  r^7 * pairedCenteredAbelOffset(r*q)
    = C'_W(q) * A4_W(q),

where A4_W is the antisymmetric quartic-scale centered discrepancy.

Changing variables s=r*q therefore yields the exact finite identity

  normalizedPairedAbelPartial(n)
    = r^6 * pairedCenteredAbelPartial(n).

Thus the global N-mu correlation is placed on the same quartic r^-6 scale as
the terminal target without any estimate.
-/

def QuarticFourSignedPolePair.normalizedPairedAbelIntegrand
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (q : ℝ) : ℝ :=
  W.normalizedOrdinateCosineD1 q
    * W.quarticScaleAntisymmetricDiscrepancy q

def QuarticFourSignedPolePair.normalizedPairedAbelPartial
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) : ℝ :=
  ∫ q in (0 : ℝ)..((n : ℝ)/(t/16)),
    W.normalizedPairedAbelIntegrand q

theorem QuarticFourSignedPolePair.normalizedPairedAbelPartial_eq_quarticScale
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.normalizedPairedAbelPartial n
      =
    (t/16)^6 * W.pairedCenteredAbelPartial n := by
  let r : ℝ := t/16
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hupper : 0 <= (n : ℝ)/r := by positivity
  have hpoint :
      (∫ q in (0 : ℝ)..((n : ℝ)/r),
        W.normalizedPairedAbelIntegrand q)
        =
      ∫ q in (0 : ℝ)..((n : ℝ)/r),
        r^7 * W.pairedCenteredAbelOffset (r*q) := by
    apply intervalIntegral.integral_congr
    intro q hq
    rw [Set.uIcc_of_le hupper] at hq
    unfold QuarticFourSignedPolePair.normalizedPairedAbelIntegrand
    have hs :=
      W.pairedCenteredAbelOffset_quarticScale
        ht (q:=q) hq.1
    dsimp [r] at hs
    symm
    exact hs
  unfold QuarticFourSignedPolePair.normalizedPairedAbelPartial
  change
    (∫ q in (0 : ℝ)..((n : ℝ)/r),
      W.normalizedPairedAbelIntegrand q)
      =
    r^6 * W.pairedCenteredAbelPartial n
  rw [hpoint, intervalIntegral.integral_const_mul]
  have hscale :=
    intervalIntegral.smul_integral_comp_mul_add
      (f:=W.pairedCenteredAbelOffset)
      (a:=(0 : ℝ))
      (b:=((n : ℝ)/r))
      r 0
  have hscale' :
      r *
        (∫ q in (0 : ℝ)..((n : ℝ)/r),
          W.pairedCenteredAbelOffset (r*q))
        =
      W.pairedCenteredAbelPartial n := by
    unfold QuarticFourSignedPolePair.pairedCenteredAbelPartial
    simpa [smul_eq_mul, hr0] using hscale
  calc
    r^7 *
        (∫ q in (0 : ℝ)..((n : ℝ)/r),
          W.pairedCenteredAbelOffset (r*q))
      =
    r^6 *
      (
        r *
        (∫ q in (0 : ℝ)..((n : ℝ)/r),
          W.pairedCenteredAbelOffset (r*q))
      ) := by ring
    _ = r^6 * W.pairedCenteredAbelPartial n := by
      rw [hscale']

theorem exists_quarticFourSignedPole_normalizedPairedAbel_tendsto :
    ∃ T0 : ℝ,
      ∀ {t : ℝ},
        (W : QuarticFourSignedPolePair t) ->
        T0 <= t ->
        Tendsto W.normalizedPairedAbelPartial atTop
          (𝓝 (- (t/16)^6 * W.signedNMuPair)) := by
  obtain ⟨T0,hT0⟩ :=
    exists_quarticFourSignedPole_combinedCenteredAbel_tendsto
  refine ⟨max T0 1,?_⟩
  intro t W ht
  have ht0 : 0 < t := by
    have h1 : 1 <= t := (le_max_right T0 1).trans ht
    linarith
  have htBase : T0 <= t :=
    (le_max_left T0 1).trans ht
  have hcombined := hT0 W htBase
  have hpaired :
      Tendsto W.pairedCenteredAbelPartial atTop
        (𝓝 (-W.signedNMuPair)) := by
    apply hcombined.congr'
    exact Filter.Eventually.of_forall fun n => by
      symm
      exact W.combinedCenteredAbelPartial_eq_paired ht0 n
  have hscaled :
      Tendsto
        (fun n : ℕ => (t/16)^6 * W.pairedCenteredAbelPartial n)
        atTop
        (𝓝 ((t/16)^6 * (-W.signedNMuPair))) :=
    tendsto_const_nhds.mul hpaired
  apply hscaled.congr'
  filter_upwards with n
  rw [W.normalizedPairedAbelPartial_eq_quarticScale ht0 n]
  ring

theorem QuarticFourSignedPolePair.quarticScaleCompletedResidual_eq_normalizedPairedLimit
    {t L : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hlim :
      Tendsto W.normalizedPairedAbelPartial atTop (𝓝 L))
    (hcanonical :
      Tendsto W.normalizedPairedAbelPartial atTop
        (𝓝 (- (t/16)^6 * W.signedNMuPair))) :
    W.quarticScaleCompletedResidual
      =
    -(1/2 : ℝ) * L
      + W.quarticScaleHorizontalRemainder := by
  have huniq := tendsto_nhds_unique hlim hcanonical
  rw [W.quarticScaleCompletedResidual_eq]
  rw [huniq]
  ring


def QuarticFourSignedPolePair.quarticScaleSymmetricWindowDiscrepancy
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (q : ℝ) : ℝ :=
  (t/16)^4
    * zetaMuCumulativeDiscrepancy
        (t - (t/16)*q)
        (t + (t/16)*q)

theorem QuarticFourSignedPolePair.quarticScaleAntisymmetricDiscrepancy_eq_literalSymmetric
    {t q : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hq : 0 <= q) :
    W.quarticScaleAntisymmetricDiscrepancy q
      =
    W.quarticScaleSymmetricWindowDiscrepancy q := by
  unfold QuarticFourSignedPolePair.quarticScaleSymmetricWindowDiscrepancy
  exact
    W.quarticScaleAntisymmetricDiscrepancy_eq_symmetricWindow
      ht hq

theorem QuarticFourSignedPolePair.normalizedPairedAbelPartial_eq_literalSymmetric
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) :
    W.normalizedPairedAbelPartial n
      =
    ∫ q in (0 : ℝ)..((n : ℝ)/(t/16)),
      W.normalizedOrdinateCosineD1 q
        * W.quarticScaleSymmetricWindowDiscrepancy q := by
  have hr : 0 < t/16 := by positivity
  have hupper : 0 <= (n : ℝ)/(t/16) := by positivity
  unfold QuarticFourSignedPolePair.normalizedPairedAbelPartial
    QuarticFourSignedPolePair.normalizedPairedAbelIntegrand
  apply intervalIntegral.integral_congr
  intro q hq
  rw [Set.uIcc_of_le hupper] at hq
  rw [W.quarticScaleAntisymmetricDiscrepancy_eq_literalSymmetric
    ht hq.1]

def QuarticFourSignedPolePair.normalizedOuterPairedAbelAt
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) : ℝ :=
  ∫ q in quarticSignedPoleCanonicalLocalRadius..((n : ℝ)/(t/16)),
    W.normalizedPairedAbelIntegrand q

theorem QuarticFourSignedPolePair.normalizedOuterPairedAbelAt_eq_literalSymmetric
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn :
      quarticSignedPoleCanonicalPhysicalHalfWidth t
        <= (n : ℝ)) :
    W.normalizedOuterPairedAbelAt n
      =
    ∫ q in quarticSignedPoleCanonicalLocalRadius..((n : ℝ)/(t/16)),
      W.normalizedOrdinateCosineD1 q
        * W.quarticScaleSymmetricWindowDiscrepancy q := by
  have hr : 0 < t/16 := by positivity
  have hlower : 0 <= quarticSignedPoleCanonicalLocalRadius :=
    quarticSignedPoleCanonicalLocalRadius_pos.le
  have hupper :
      quarticSignedPoleCanonicalLocalRadius
        <= (n : ℝ)/(t/16) := by
    rw [le_div_iff₀ hr]
    unfold quarticSignedPoleCanonicalPhysicalHalfWidth at hn
    exact hn
  unfold QuarticFourSignedPolePair.normalizedOuterPairedAbelAt
    QuarticFourSignedPolePair.normalizedPairedAbelIntegrand
  apply intervalIntegral.integral_congr
  intro q hq
  rw [Set.uIcc_of_le hupper] at hq
  rw [W.quarticScaleAntisymmetricDiscrepancy_eq_literalSymmetric
    ht (hlower.trans hq.1)]

theorem QuarticFourSignedPolePair.normalizedOuterPairedAbelAt_eq_quarticScale
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn :
      quarticSignedPoleCanonicalPhysicalHalfWidth t
        <= (n : ℝ)) :
    W.normalizedOuterPairedAbelAt n
      =
    (t/16)^6 * W.canonicalOuterPairedAbelAt n := by
  let r : ℝ := t/16
  let eta : ℝ := quarticSignedPoleCanonicalLocalRadius
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hr0 : r ≠ 0 := ne_of_gt hr
  have heta : 0 < eta := by
    dsimp [eta]
    exact quarticSignedPoleCanonicalLocalRadius_pos
  have hupper : eta <= (n : ℝ)/r := by
    rw [le_div_iff₀ hr]
    dsimp [eta,r]
    unfold quarticSignedPoleCanonicalPhysicalHalfWidth at hn
    exact hn
  have hpoint :
      (∫ q in eta..((n : ℝ)/r),
        W.normalizedPairedAbelIntegrand q)
        =
      ∫ q in eta..((n : ℝ)/r),
        r^7 * W.pairedCenteredAbelOffset (r*q) := by
    apply intervalIntegral.integral_congr
    intro q hq
    rw [Set.uIcc_of_le hupper] at hq
    unfold QuarticFourSignedPolePair.normalizedPairedAbelIntegrand
    have hs :=
      W.pairedCenteredAbelOffset_quarticScale
        ht (q:=q) (heta.le.trans hq.1)
    dsimp [r] at hs
    symm
    exact hs
  unfold QuarticFourSignedPolePair.normalizedOuterPairedAbelAt
  change
    (∫ q in eta..((n : ℝ)/r),
      W.normalizedPairedAbelIntegrand q)
      =
    r^6 * W.canonicalOuterPairedAbelAt n
  rw [hpoint, intervalIntegral.integral_const_mul]
  have hscale :=
    intervalIntegral.smul_integral_comp_mul_add
      (f:=W.pairedCenteredAbelOffset)
      (a:=eta)
      (b:=((n : ℝ)/r))
      r 0
  have hscale' :
      r *
        (∫ q in eta..((n : ℝ)/r),
          W.pairedCenteredAbelOffset (r*q))
        =
      W.canonicalOuterPairedAbelAt n := by
    unfold QuarticFourSignedPolePair.canonicalOuterPairedAbelAt
    dsimp [eta,r]
    simpa [smul_eq_mul, hr0,
      quarticSignedPoleCanonicalPhysicalHalfWidth] using hscale
  calc
    r^7 *
        (∫ q in eta..((n : ℝ)/r),
          W.pairedCenteredAbelOffset (r*q))
      =
    r^6 *
      (
        r *
        (∫ q in eta..((n : ℝ)/r),
          W.pairedCenteredAbelOffset (r*q))
      ) := by ring
    _ = r^6 * W.canonicalOuterPairedAbelAt n := by
      rw [hscale']

def QuarticFourSignedPolePair.quarticScaleOuterPairedHorizontalAt
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) : ℝ :=
  -(1/2 : ℝ) * W.normalizedOuterPairedAbelAt n
    + W.quarticScaleHorizontalRemainder

theorem QuarticFourSignedPolePair.quarticScaleOuterPairedHorizontalAt_eq
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn :
      quarticSignedPoleCanonicalPhysicalHalfWidth t
        <= (n : ℝ)) :
    W.quarticScaleOuterPairedHorizontalAt n
      =
    (t/16)^6 * W.canonicalOuterPairedHorizontalAt n := by
  unfold QuarticFourSignedPolePair.quarticScaleOuterPairedHorizontalAt
    QuarticFourSignedPolePair.quarticScaleHorizontalRemainder
    QuarticFourSignedPolePair.canonicalOuterPairedHorizontalAt
  rw [W.normalizedOuterPairedAbelAt_eq_quarticScale ht n hn]
  ring


/-!
## Dimensionless outer-terminal exhaustion

The normalized outer Abel integral already owns the entire vertical
zero-distribution channel outside the canonical local radius. Add the exact
horizontal correction and subtract the fixed literal-vs-paired local
correction on the same r^6 scale.

The resulting finite scalar converges to r^6 times the canonical signed high
residual. This is the final representation recut before genuinely new
zero-distribution analysis.
-/

def QuarticFourSignedPolePair.quarticScaleCanonicalLocalCorrection
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) : ℝ :=
  (t/16)^6 * W.canonicalLiteralVsPairedLocalCorrection

def QuarticFourSignedPolePair.quarticScaleOuterTerminalAt
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (n : ℕ) : ℝ :=
  W.quarticScaleOuterPairedHorizontalAt n
    - W.quarticScaleCanonicalLocalCorrection

theorem QuarticFourSignedPolePair.normalizedPairedAbelPartial_eq_local_add_outer
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn :
      quarticSignedPoleCanonicalPhysicalHalfWidth t
        <= (n : ℝ)) :
    W.normalizedPairedAbelPartial n
      =
    (t/16)^6 * W.canonicalLocalPairedAbel
      + W.normalizedOuterPairedAbelAt n := by
  rw [W.normalizedPairedAbelPartial_eq_quarticScale ht n,
      W.normalizedOuterPairedAbelAt_eq_quarticScale ht n hn,
      W.pairedCenteredAbelPartial_eq_local_add_outer ht n hn]
  ring

theorem exists_quarticFourSignedPole_normalizedOuterPairedAbel_tendsto :
    ∃ T0 : ℝ, 1 <= T0 ∧
      ∀ {t : ℝ},
        (W : QuarticFourSignedPolePair t) ->
        T0 <= t ->
        Tendsto W.normalizedOuterPairedAbelAt atTop
          (𝓝
            (
              - (t/16)^6 * W.signedNMuPair
              - (t/16)^6 * W.canonicalLocalPairedAbel
            )) := by
  obtain ⟨Tbase,hTbase⟩ :=
    exists_quarticFourSignedPole_normalizedPairedAbel_tendsto
  let T0 : ℝ := max Tbase 1
  refine ⟨T0,le_max_right _ _,?_⟩
  intro t W ht
  have ht0 : 0 < t := by
    have h1 : 1 <= t := (le_max_right Tbase 1).trans ht
    linarith
  have htBase : Tbase <= t :=
    (le_max_left Tbase 1).trans ht
  have htotal := hTbase W htBase
  let N := quarticSignedPoleCanonicalLocalExhaustionIndex t
  have hN :
      quarticSignedPoleCanonicalPhysicalHalfWidth t < (N : ℝ) := by
    dsimp [N]
    exact quarticSignedPoleCanonicalLocalExhaustionIndex_spec t
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        quarticSignedPoleCanonicalPhysicalHalfWidth t <= (n : ℝ) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    have hNN : (N : ℝ) <= (n : ℝ) := by exact_mod_cast hn
    exact hN.le.trans hNN
  have heq :
      ∀ᶠ n : ℕ in atTop,
        W.normalizedOuterPairedAbelAt n
          =
        W.normalizedPairedAbelPartial n
          - (t/16)^6 * W.canonicalLocalPairedAbel := by
    filter_upwards [hevent] with n hn
    rw [W.normalizedPairedAbelPartial_eq_local_add_outer ht0 n hn]
    ring
  have hsub :
      Tendsto
        (fun n : ℕ =>
          W.normalizedPairedAbelPartial n
            - (t/16)^6 * W.canonicalLocalPairedAbel)
        atTop
        (𝓝
          (
            - (t/16)^6 * W.signedNMuPair
            - (t/16)^6 * W.canonicalLocalPairedAbel
          )) :=
    htotal.sub_const _
  exact hsub.congr' heq.symm

theorem exists_quarticFourSignedPole_quarticScaleOuterPairedHorizontal_tendsto :
    ∃ T0 : ℝ, 1 <= T0 ∧
      ∀ {t : ℝ},
        (W : QuarticFourSignedPolePair t) ->
        T0 <= t ->
        Tendsto W.quarticScaleOuterPairedHorizontalAt atTop
          (𝓝 ((t/16)^6 * W.canonicalFarBoundaryCoupledCompensation)) := by
  obtain ⟨T0,hT01,hT0⟩ :=
    exists_quarticFourSignedPole_normalizedOuterPairedAbel_tendsto
  refine ⟨T0,hT01,?_⟩
  intro t W ht
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) (hT01.trans ht)
  have houter := hT0 W ht
  have hscaled :
      Tendsto
        (fun n : ℕ =>
          -(1/2 : ℝ) * W.normalizedOuterPairedAbelAt n
            + W.quarticScaleHorizontalRemainder)
        atTop
        (𝓝
          (
            -(1/2 : ℝ) *
              (
                - (t/16)^6 * W.signedNMuPair
                - (t/16)^6 * W.canonicalLocalPairedAbel
              )
            + W.quarticScaleHorizontalRemainder
          )) :=
    (tendsto_const_nhds.mul houter).add_const _
  have htarget :
      -(1/2 : ℝ) *
          (
            - (t/16)^6 * W.signedNMuPair
            - (t/16)^6 * W.canonicalLocalPairedAbel
          )
        + W.quarticScaleHorizontalRemainder
      =
      (t/16)^6 * W.canonicalFarBoundaryCoupledCompensation := by
    unfold QuarticFourSignedPolePair.quarticScaleHorizontalRemainder
    rw [W.canonicalFarBoundaryCoupledCompensation_eq_completed_sub_localPaired ht0]
    unfold QuarticFourSignedPolePair.completedSignedResidual
      QuarticFourSignedPolePair.canonicalLocalPairedContribution
    ring
  unfold QuarticFourSignedPolePair.quarticScaleOuterPairedHorizontalAt
  rw [← htarget]
  exact hscaled

theorem exists_quarticFourSignedPole_quarticScaleOuterTerminal_tendsto :
    ∃ T0 : ℝ, 1 <= T0 ∧
      ∀ {t : ℝ},
        (W : QuarticFourSignedPolePair t) ->
        T0 <= t ->
        Tendsto W.quarticScaleOuterTerminalAt atTop
          (𝓝 ((t/16)^6 * W.canonicalSignedHighResidual)) := by
  obtain ⟨T0,hT01,hT0⟩ :=
    exists_quarticFourSignedPole_quarticScaleOuterPairedHorizontal_tendsto
  refine ⟨T0,hT01,?_⟩
  intro t W ht
  have houter := hT0 W ht
  have hsub :
      Tendsto
        (fun n : ℕ =>
          W.quarticScaleOuterPairedHorizontalAt n
            - W.quarticScaleCanonicalLocalCorrection)
        atTop
        (𝓝
          (
            (t/16)^6 * W.canonicalFarBoundaryCoupledCompensation
              - W.quarticScaleCanonicalLocalCorrection
          )) :=
    houter.sub_const _
  have htarget :
      (t/16)^6 * W.canonicalFarBoundaryCoupledCompensation
          - W.quarticScaleCanonicalLocalCorrection
        =
      (t/16)^6 * W.canonicalSignedHighResidual := by
    unfold QuarticFourSignedPolePair.quarticScaleCanonicalLocalCorrection
      QuarticFourSignedPolePair.canonicalSignedHighResidual
    ring
  unfold QuarticFourSignedPolePair.quarticScaleOuterTerminalAt
  rw [← htarget]
  exact hsub


/-!
## Finite-Q terminal interface

Because the dimensionless outer-terminal sequence converges to r^6 H_W, the
strict canonical high cut is equivalent to an eventual finite-Q bound with a
positive slack.  This removes improper limits from the statement a future
ordinary analytic proof must establish.
-/

def QuarticFourSignedPolePair.QuarticScaleOuterTerminalEventuallyBelowMargin
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (EV : ℝ) : Prop :=
  ∃ eps : ℝ, 0 < eps ∧
    ∀ᶠ n : ℕ in atTop,
      W.quarticScaleOuterTerminalAt n
        <=
      (t/16)^6 * W.postSixthTerminalResidualMargin rho EV - eps

theorem QuarticFourSignedPolePair.quarticScaleOuterTerminalEventuallyBelowMargin_iff_highCut
    {t EV : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (rho : Zeros)
    (hlim :
      Tendsto W.quarticScaleOuterTerminalAt atTop
        (𝓝 ((t/16)^6 * W.canonicalSignedHighResidual))) :
    W.QuarticScaleOuterTerminalEventuallyBelowMargin rho EV
      ↔
    W.PostSixthCanonicalSignedHighCut rho EV := by
  let L : ℝ := (t/16)^6 * W.canonicalSignedHighResidual
  let M : ℝ := (t/16)^6 * W.postSixthTerminalResidualMargin rho EV
  have hr6 : 0 < (t/16)^6 := by positivity
  constructor
  · rintro ⟨eps,heps,hev⟩
    have hle :
        L <= M - eps := by
      apply le_of_tendsto hlim
      exact hev
    unfold QuarticFourSignedPolePair.PostSixthCanonicalSignedHighCut
    dsimp [L,M] at hle
    have hscaled :
        (t/16)^6 * W.canonicalSignedHighResidual
          <
        (t/16)^6 * W.postSixthTerminalResidualMargin rho EV := by
      linarith
    exact (mul_lt_mul_left hr6).mp hscaled
  · intro hcut
    unfold QuarticFourSignedPolePair.PostSixthCanonicalSignedHighCut at hcut
    have hscaled :
        L < M := by
      dsimp [L,M]
      exact (mul_lt_mul_left hr6).2 hcut
    let eps : ℝ := (M-L)/2
    have heps : 0 < eps := by
      dsimp [eps]
      linarith
    have htarget : L < M - eps := by
      dsimp [eps]
      linarith
    have hev :
        ∀ᶠ n : ℕ in atTop,
          W.quarticScaleOuterTerminalAt n < M - eps :=
      (tendsto_order.1 hlim).2 _ htarget
    refine ⟨eps,heps,?_⟩
    filter_upwards [hev] with n hn
    exact hn.le

def QuarticScaleOuterTerminalFiniteQUniformHighEstimate
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
        W.QuarticScaleOuterTerminalEventuallyBelowMargin
          rho (quarticSignedPoleCanonicalV4Error CV t)

theorem exists_quarticSignedPoleFixedHigh_finiteQOuterTerminalEstimate_excludes_offLine :
    ∃ CV T : ℝ,
      0 <= CV
        ∧ quarticPlattTrudgianCutoff <= T
        ∧
      (
        QuarticScaleOuterTerminalFiniteQUniformHighEstimate CV T
        ->
        ∀ {t : ℝ},
          T < t ->
          ∀ {rho : Zeros},
            (rho : ℂ).im = t ->
            heightOf rho ≠ 0 ->
            False
      ) := by
  obtain ⟨Tlim,hTlim1,hTlim⟩ :=
    exists_quarticFourSignedPole_quarticScaleOuterTerminal_tendsto
  obtain ⟨CV,Tbase,hCV,hPT,hcompile⟩ :=
    exists_quarticSignedPoleFixedHigh_compiles_selectedLiteralFarMinusMuHighCut
  let T : ℝ := max Tbase Tlim
  refine ⟨CV,T,hCV,?_,?_⟩
  · exact hPT.trans (le_max_left _ _)
  · intro hfinite t ht rho him hoff
    have htBase : Tbase < t :=
      lt_of_le_of_lt (le_max_left Tbase Tlim) ht
    have htLim : Tlim <= t :=
      (le_max_right Tbase Tlim).trans ht.le
    obtain ⟨W,hS,hM6lo,hM6neg,hband,hfiniteCut⟩ :=
      hfinite ht him hoff
    have ht0 : 0 < t := by
      have hPT200 := quarticPlattTrudgianCutoff_gt_twoHundred
      have hPTt : quarticPlattTrudgianCutoff < t :=
        lt_of_le_of_lt (hPT.trans (le_max_left _ _)) ht
      linarith
    have hlim := hTlim W htLim
    have hcanonical :
        W.PostSixthCanonicalSignedHighCut rho
          (quarticSignedPoleCanonicalV4Error CV t) :=
      (W.quarticScaleOuterTerminalEventuallyBelowMargin_iff_highCut
        ht0 rho hlim).1 hfiniteCut
    have hliteral :
        (1/2 : ℝ)
          *
          (
            W.canonicalLiteralFarPairSource
            -
            ∫ tau : ℝ,
              W.signedOrdinateTest tau * Zeta23.mu tau
          )
          <
        W.postSixthTerminalResidualMargin rho
          (quarticSignedPoleCanonicalV4Error CV t) :=
      (W.postSixthCanonicalSignedHighCut_iff_literalFar
        (by
          have hPT200 := quarticPlattTrudgianCutoff_gt_twoHundred
          have hPTt : quarticPlattTrudgianCutoff < t :=
            lt_of_le_of_lt (hPT.trans (le_max_left _ _)) ht
          linarith)
        rho).1 hcanonical
    exact
      hcompile htBase him hoff
        ⟨W,hS,hM6lo,hM6neg,hband,hliteral⟩


/-!
## Four-primitive scale cancellation

The normalized outer wall contains

  A4(q) = r^4 * D(t-r*q,t+r*q),   r=t/16.

A pointwise estimate on A4 is far too expensive.  But after four primitives in
the normalized variable, the apparent r^4 loss cancels *exactly* against the
affine change of variables and the cubic Cesaro kernel.

Define the fourth primitive anchored at the canonical normalized cut eta0:

  P4_q(Q)
    = ∫_[eta0,Q] ((Q-q)^3/6) * A4(q) dq.

Define its physical-halfwidth counterpart:

  P4_s(Q)
    = ∫_[r*eta0,r*Q]
        ((r*Q-s)^3/6) * D(t-s,t+s) ds.

Then P4_q(Q)=P4_s(Q) exactly.  This is the first nontrivial mechanism in the
current reduction that can supply the four missing inverse powers without a
pointwise r^-4 discrepancy estimate.

No bound on this primitive is asserted here.
-/

def QuarticFourSignedPolePair.outerSymmetricDiscrepancyFourthPrimitive
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (Q : ℝ) : ℝ :=
  ∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
    ((Q-q)^3 / 6)
      * W.quarticScaleSymmetricWindowDiscrepancy q

def QuarticFourSignedPolePair.outerSymmetricDiscrepancyFourthPhysicalPrimitive
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (Q : ℝ) : ℝ :=
  let r := t/16
  let eta := quarticSignedPoleCanonicalLocalRadius
  ∫ s in (r*eta)..(r*Q),
    ((r*Q-s)^3 / 6)
      * zetaMuCumulativeDiscrepancy (t-s) (t+s)

theorem QuarticFourSignedPolePair.outerSymmetricDiscrepancyFourthPrimitive_eq_physical
    {t Q : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.outerSymmetricDiscrepancyFourthPrimitive Q
      =
    W.outerSymmetricDiscrepancyFourthPhysicalPrimitive Q := by
  let r : ℝ := t/16
  let eta : ℝ := quarticSignedPoleCanonicalLocalRadius
  let f : ℝ -> ℝ := fun s =>
    ((r*Q-s)^3 / 6)
      * zetaMuCumulativeDiscrepancy (t-s) (t+s)
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hscale :=
    intervalIntegral.smul_integral_comp_mul_add
      (f:=f) (a:=eta) (b:=Q) r 0
  unfold QuarticFourSignedPolePair.outerSymmetricDiscrepancyFourthPrimitive
    QuarticFourSignedPolePair.outerSymmetricDiscrepancyFourthPhysicalPrimitive
    QuarticFourSignedPolePair.quarticScaleSymmetricWindowDiscrepancy
  dsimp [r,eta] at hscale ⊢
  rw [show
      (fun q : ℝ =>
        ((Q-q)^3 / 6)
          *
        ((t/16)^4
          * zetaMuCumulativeDiscrepancy
              (t-(t/16)*q)
              (t+(t/16)*q)))
      =
      fun q =>
        (t/16) *
          (
            (((t/16)*Q - (t/16)*q)^3 / 6)
              *
            zetaMuCumulativeDiscrepancy
              (t-(t/16)*q)
              (t+(t/16)*q)
          ) by
        funext q
        ring]
  rw [intervalIntegral.integral_const_mul]
  simpa [smul_eq_mul] using hscale

def QuarticFourSignedPolePair.OuterFourthPrimitiveUniformBound
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (B : ℝ) : Prop :=
  ∀ Q : ℝ,
    quarticSignedPoleCanonicalLocalRadius <= Q ->
    |W.outerSymmetricDiscrepancyFourthPhysicalPrimitive Q| <= B

theorem QuarticFourSignedPolePair.outerFourthPrimitiveUniformBound_normalized
    {t B Q : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hB : W.OuterFourthPrimitiveUniformBound B)
    (hQ : quarticSignedPoleCanonicalLocalRadius <= Q) :
    |W.outerSymmetricDiscrepancyFourthPrimitive Q| <= B := by
  rw [W.outerSymmetricDiscrepancyFourthPrimitive_eq_physical ht]
  exact hB Q hQ

/-!
Source firewall.

A future donor for OuterFourthPrimitiveUniformBound must be unconditional in
the RH proof context.  Conditional pointwise bounds for the classical
iterated argument functions S_n(t) may be useful as diagnostics, but importing
an RH-conditional S_n theorem here would be circular and therefore cannot pay
the Clay-facing analytic debt.
-/

def OuterFourthPrimitiveDonorBoundary : Prop :=
  True

theorem outerFourthPrimitiveDonorBoundary : OuterFourthPrimitiveDonorBoundary := by
  trivial

end Synthesis
