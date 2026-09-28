import Synthesis.RiemannProjectiveQuarticFourWindowSignedPoleFourierMass
import Synthesis.RiemannQuarticFourPrimitiveIBP
import Synthesis.RiemannCompactCosineSchwartzDecay

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


/-!
## Fourfold IBP specialization to the literal outer discrepancy

This theorem is the direct bridge from the finite-Q carrier to the canonical
anchored primitive ladder.  The only remaining measure-theoretic premise is
finite-interval integrability of the literal symmetric discrepancy itself.
No differentiability of the zero staircase is assumed.
-/

theorem QuarticFourSignedPolePair.normalizedOuterPairedAbelAt_fourfold_ibp
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn :
      quarticSignedPoleCanonicalPhysicalHalfWidth t
        <= (n : ℝ))
    (hA :
      IntervalIntegrable
        W.quarticScaleSymmetricWindowDiscrepancy
        volume
        quarticSignedPoleCanonicalLocalRadius
        ((n : ℝ)/(t/16))) :
    W.normalizedOuterPairedAbelAt n
      =
    fourfoldIBPBoundary
      W.normalizedOrdinateCosineD1
      (compactCosineD2
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t))
      (compactCosineD3
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t))
      (compactCosineD4
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t))
      (anchoredPrimitive1
        W.quarticScaleSymmetricWindowDiscrepancy
        quarticSignedPoleCanonicalLocalRadius)
      (anchoredPrimitive2
        W.quarticScaleSymmetricWindowDiscrepancy
        quarticSignedPoleCanonicalLocalRadius)
      (anchoredPrimitive3
        W.quarticScaleSymmetricWindowDiscrepancy
        quarticSignedPoleCanonicalLocalRadius)
      (anchoredPrimitive4
        W.quarticScaleSymmetricWindowDiscrepancy
        quarticSignedPoleCanonicalLocalRadius)
      quarticSignedPoleCanonicalLocalRadius
      ((n : ℝ)/(t/16))
      +
    ∫ q in quarticSignedPoleCanonicalLocalRadius..((n : ℝ)/(t/16)),
      compactCosineD5
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t) q
        *
      anchoredPrimitive4
        W.quarticScaleSymmetricWindowDiscrepancy
        quarticSignedPoleCanonicalLocalRadius q := by
  rw [W.normalizedOuterPairedAbelAt_eq_literalSymmetric ht n hn]
  unfold QuarticFourSignedPolePair.normalizedOrdinateCosineD1
  exact
    compactCosineD1_fourfold_ibp_anchored
      (quarticFourSignedPoleCombinedProfile_continuous W.Rpos)
      (quarticFourSignedPoleCombinedProfile_compact W.Rpos)
      hA


/-!
## Quartic cap carrier for the physical fourth primitive

For physical half-widths s0 <= S define the cap

  w(y) = (max 0 (S - max s0 |y-t|))^4 / 24.

It is constant on the already-paid inner window |y-t| <= s0, quartic on the
annulus s0 <= |y-t| <= S, and zero outside the outer symmetric window.

The expected Fubini weld is

  physicalFourthPrimitive(S)
    =
  zetaWindowMinusMuPair (t-S) (t+S) w.

That equality is intentionally not asserted below yet; this section only
constructs the literal weighted-pair carrier and pays its elementary geometry.
-/

def quarticSymmetricCapWeight
    (t s0 S y : ℝ) : ℝ :=
  (max 0 (S - max s0 |y-t|))^4 / 24

theorem quarticSymmetricCapWeight_nonneg
    (t s0 S y : ℝ) :
    0 <= quarticSymmetricCapWeight t s0 S y := by
  unfold quarticSymmetricCapWeight
  positivity

theorem quarticSymmetricCapWeight_eq_inner
    {t s0 S y : ℝ}
    (hs0 : 0 <= s0)
    (hsS : s0 <= S)
    (hy : |y-t| <= s0) :
    quarticSymmetricCapWeight t s0 S y
      =
    (S-s0)^4 / 24 := by
  unfold quarticSymmetricCapWeight
  rw [max_eq_left hy]
  rw [max_eq_right]
  · rfl
  · linarith

theorem quarticSymmetricCapWeight_eq_annulus
    {t s0 S y : ℝ}
    (hs0y : s0 <= |y-t|)
    (hyS : |y-t| <= S) :
    quarticSymmetricCapWeight t s0 S y
      =
    (S-|y-t|)^4 / 24 := by
  unfold quarticSymmetricCapWeight
  rw [max_eq_right hs0y]
  rw [max_eq_right]
  · rfl
  · linarith

theorem quarticSymmetricCapWeight_eq_zero_of_outer
    {t s0 S y : ℝ}
    (hSy : S <= |y-t|) :
    quarticSymmetricCapWeight t s0 S y = 0 := by
  unfold quarticSymmetricCapWeight
  have hmax : S <= max s0 |y-t| :=
    hSy.trans (le_max_right _ _)
  rw [max_eq_left]
  · norm_num
  · linarith

theorem quarticSymmetricCapWeight_at_outer_right
    {t s0 S : ℝ}
    (hsS : s0 <= S) :
    quarticSymmetricCapWeight t s0 S (t+S) = 0 := by
  apply quarticSymmetricCapWeight_eq_zero_of_outer
  rw [show t+S-t = S by ring]
  exact le_abs_self S

theorem quarticSymmetricCapWeight_at_outer_left
    {t s0 S : ℝ}
    (hsS : s0 <= S) :
    quarticSymmetricCapWeight t s0 S (t-S) = 0 := by
  apply quarticSymmetricCapWeight_eq_zero_of_outer
  rw [show t-S-t = -S by ring, abs_neg]
  exact le_abs_self S

def QuarticFourSignedPolePair.physicalFourthCapPair
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (S : ℝ) : ℝ :=
  let s0 :=
    quarticSignedPoleCanonicalPhysicalHalfWidth t
  zetaWindowMinusMuPair
    (t-S) (t+S)
    (quarticSymmetricCapWeight t s0 S)

def QuarticFourSignedPolePair.physicalFourthCapWeight
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (S : ℝ) : ℝ -> ℝ :=
  quarticSymmetricCapWeight
    t quarticSignedPoleCanonicalPhysicalHalfWidth t S

theorem QuarticFourSignedPolePair.physicalFourthCapWeight_nonneg
    {t S y : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.physicalFourthCapWeight S y :=
  quarticSymmetricCapWeight_nonneg _ _ _ _


/-!
## Upper IBP boundary: rapid decay versus polynomial primitive growth

The upper Q-boundary does not need a sharp RvM estimate.  Any fixed polynomial
growth envelope for the four anchored primitives is enough because the
selected compact profile is C-infinity and its cosine derivative tower is
Schwartz-rapidly decaying.

We deliberately keep the lower eta0 boundary separate.
-/

def QuarticFourSignedPolePair.OuterPrimitivePolynomialEnvelope
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (B1 B2 B3 B4 : ℝ) : Prop :=
  ∀ Q : ℝ,
    max 1 quarticSignedPoleCanonicalLocalRadius <= Q ->
    |anchoredPrimitive1
      W.quarticScaleSymmetricWindowDiscrepancy
      quarticSignedPoleCanonicalLocalRadius Q|
      <= B1 * Q^2
    ∧
    |anchoredPrimitive2
      W.quarticScaleSymmetricWindowDiscrepancy
      quarticSignedPoleCanonicalLocalRadius Q|
      <= B2 * Q^3
    ∧
    |anchoredPrimitive3
      W.quarticScaleSymmetricWindowDiscrepancy
      quarticSignedPoleCanonicalLocalRadius Q|
      <= B3 * Q^4
    ∧
    |anchoredPrimitive4
      W.quarticScaleSymmetricWindowDiscrepancy
      quarticSignedPoleCanonicalLocalRadius Q|
      <= B4 * Q^5

theorem mul_abs_le_invSq_of_rapid_decay_and_poly
    {C P K B Q : ℝ}
    {m d : ℕ}
    (hQ : 1 <= Q)
    (hm : m = d + 2)
    (hK : 0 <= K)
    (hB : 0 <= B)
    (hC : |Q|^m * |C| <= K)
    (hP : |P| <= B * Q^d) :
    |C * P| <= K * B / Q^2 := by
  subst m
  have hQpos : 0 < Q := lt_of_lt_of_le (by norm_num) hQ
  have hQabs : |Q| = Q := abs_of_nonneg hQ.le
  rw [abs_mul,hQabs] at hC ⊢
  have hQpow : 0 < Q^(d+2) := pow_pos hQpos _
  have hC' : |C| <= K / Q^(d+2) := by
    rw [le_div_iff₀ hQpow]
    simpa [mul_comm] using hC
  calc
    |C| * |P|
      <= (K / Q^(d+2)) * (B * Q^d) := by
        exact mul_le_mul hC' hP (abs_nonneg _) (by positivity)
    _ = K * B / Q^2 := by
        field_simp [ne_of_gt hQpos]
        ring

theorem QuarticFourSignedPolePair.exists_upperIBPBoundary_invSq_bound
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    {B1 B2 B3 B4 : ℝ}
    (hB1 : 0 <= B1)
    (hB2 : 0 <= B2)
    (hB3 : 0 <= B3)
    (hB4 : 0 <= B4)
    (henv : W.OuterPrimitivePolynomialEnvelope B1 B2 B3 B4) :
    ∃ K : ℝ, 0 < K ∧
      ∀ Q : ℝ,
        max 1 quarticSignedPoleCanonicalLocalRadius <= Q ->
        |fourfoldIBPUpperBoundary
          W.normalizedOrdinateCosineD1
          (compactCosineD2
            (quarticFourSignedPoleCombinedProfile
              W.R W.muHalf W.muTwo t))
          (compactCosineD3
            (quarticFourSignedPoleCombinedProfile
              W.R W.muHalf W.muTwo t))
          (compactCosineD4
            (quarticFourSignedPoleCombinedProfile
              W.R W.muHalf W.muTwo t))
          (anchoredPrimitive1
            W.quarticScaleSymmetricWindowDiscrepancy
            quarticSignedPoleCanonicalLocalRadius)
          (anchoredPrimitive2
            W.quarticScaleSymmetricWindowDiscrepancy
            quarticSignedPoleCanonicalLocalRadius)
          (anchoredPrimitive3
            W.quarticScaleSymmetricWindowDiscrepancy
            quarticSignedPoleCanonicalLocalRadius)
          (anchoredPrimitive4
            W.quarticScaleSymmetricWindowDiscrepancy
            quarticSignedPoleCanonicalLocalRadius)
          Q|
        <= K / Q^2 := by
  let P :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  have hPs : ContDiff ℝ (⊤ : ℕ∞) P := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_contDiff_n W.Rpos ⊤
  have hPc : HasCompactSupport P := by
    dsimp [P]
    exact quarticFourSignedPoleCombinedProfile_compact W.Rpos
  obtain ⟨K1,hK1,hD1⟩ :=
    compactCosineD1_rapid_decay hPc hPs 4
  obtain ⟨K2,hK2,hD2⟩ :=
    compactCosineD2_rapid_decay hPc hPs 5
  obtain ⟨K3,hK3,hD3⟩ :=
    compactCosineD3_rapid_decay hPc hPs 6
  obtain ⟨K4,hK4,hD4⟩ :=
    compactCosineD4_rapid_decay hPc hPs 7
  let K := K1*B1 + K2*B2 + K3*B3 + K4*B4 + 1
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K,hK,?_⟩
  intro Q hQ
  have hQ1 : 1 <= Q := (le_max_left 1 _).trans hQ
  obtain ⟨hP1,hP2,hP3,hP4⟩ := henv Q hQ
  have h1 :=
    mul_abs_le_invSq_of_rapid_decay_and_poly
      hQ1 rfl hK1.le hB1 (hD1 Q) hP1
  have h2 :=
    mul_abs_le_invSq_of_rapid_decay_and_poly
      hQ1 rfl hK2.le hB2 (hD2 Q) hP2
  have h3 :=
    mul_abs_le_invSq_of_rapid_decay_and_poly
      hQ1 rfl hK3.le hB3 (hD3 Q) hP3
  have h4 :=
    mul_abs_le_invSq_of_rapid_decay_and_poly
      hQ1 rfl hK4.le hB4 (hD4 Q) hP4
  unfold fourfoldIBPUpperBoundary
  have habs :=
    abs_add
      (W.normalizedOrdinateCosineD1 Q *
        anchoredPrimitive1 W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius Q
       -
       compactCosineD2 P Q *
        anchoredPrimitive2 W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius Q)
      (compactCosineD3 P Q *
        anchoredPrimitive3 W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius Q
       -
       compactCosineD4 P Q *
        anchoredPrimitive4 W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius Q)
  have hleft :=
    abs_sub
      (W.normalizedOrdinateCosineD1 Q *
        anchoredPrimitive1 W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius Q)
      (compactCosineD2 P Q *
        anchoredPrimitive2 W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius Q)
  have hright :=
    abs_sub
      (compactCosineD3 P Q *
        anchoredPrimitive3 W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius Q)
      (compactCosineD4 P Q *
        anchoredPrimitive4 W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius Q)
  dsimp [P] at h1 h2 h3 h4 ⊢
  have hsum :
      |W.normalizedOrdinateCosineD1 Q *
          anchoredPrimitive1 W.quarticScaleSymmetricWindowDiscrepancy
            quarticSignedPoleCanonicalLocalRadius Q
        -
        compactCosineD2
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t) Q *
          anchoredPrimitive2 W.quarticScaleSymmetricWindowDiscrepancy
            quarticSignedPoleCanonicalLocalRadius Q
        +
        (
          compactCosineD3
            (quarticFourSignedPoleCombinedProfile
              W.R W.muHalf W.muTwo t) Q *
            anchoredPrimitive3 W.quarticScaleSymmetricWindowDiscrepancy
              quarticSignedPoleCanonicalLocalRadius Q
          -
          compactCosineD4
            (quarticFourSignedPoleCombinedProfile
              W.R W.muHalf W.muTwo t) Q *
            anchoredPrimitive4 W.quarticScaleSymmetricWindowDiscrepancy
              quarticSignedPoleCanonicalLocalRadius Q
        )|
      <= (K1*B1 + K2*B2 + K3*B3 + K4*B4) / Q^2 := by
    calc
      _ <=
        |W.normalizedOrdinateCosineD1 Q *
          anchoredPrimitive1 W.quarticScaleSymmetricWindowDiscrepancy
            quarticSignedPoleCanonicalLocalRadius Q
        -
        compactCosineD2
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t) Q *
          anchoredPrimitive2 W.quarticScaleSymmetricWindowDiscrepancy
            quarticSignedPoleCanonicalLocalRadius Q|
        +
        |compactCosineD3
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t) Q *
          anchoredPrimitive3 W.quarticScaleSymmetricWindowDiscrepancy
            quarticSignedPoleCanonicalLocalRadius Q
        -
        compactCosineD4
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t) Q *
          anchoredPrimitive4 W.quarticScaleSymmetricWindowDiscrepancy
            quarticSignedPoleCanonicalLocalRadius Q| := habs
      _ <=
        (K1*B1 / Q^2 + K2*B2 / Q^2)
        + (K3*B3 / Q^2 + K4*B4 / Q^2) := by
          exact add_le_add
            (hleft.trans (add_le_add h1 h2))
            (hright.trans (add_le_add h3 h4))
      _ = (K1*B1 + K2*B2 + K3*B3 + K4*B4) / Q^2 := by ring
  exact hsum.trans <| by
    dsimp [K]
    have hQ2 : 0 < Q^2 := by positivity
    rw [div_le_div_iff₀ hQ2]
    nlinarith

end Synthesis


theorem QuarticFourSignedPolePair.normalizedOuterPairedAbelAt_eq_upperBoundary_add_fifthInterior
    {t : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (n : ℕ)
    (hn :
      quarticSignedPoleCanonicalPhysicalHalfWidth t
        <= (n : ℝ))
    (hA :
      IntervalIntegrable
        W.quarticScaleSymmetricWindowDiscrepancy
        volume
        quarticSignedPoleCanonicalLocalRadius
        ((n : ℝ)/(t/16))) :
    W.normalizedOuterPairedAbelAt n
      =
    fourfoldIBPUpperBoundary
      W.normalizedOrdinateCosineD1
      (compactCosineD2
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t))
      (compactCosineD3
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t))
      (compactCosineD4
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t))
      (anchoredPrimitive1
        W.quarticScaleSymmetricWindowDiscrepancy
        quarticSignedPoleCanonicalLocalRadius)
      (anchoredPrimitive2
        W.quarticScaleSymmetricWindowDiscrepancy
        quarticSignedPoleCanonicalLocalRadius)
      (anchoredPrimitive3
        W.quarticScaleSymmetricWindowDiscrepancy
        quarticSignedPoleCanonicalLocalRadius)
      (anchoredPrimitive4
        W.quarticScaleSymmetricWindowDiscrepancy
        quarticSignedPoleCanonicalLocalRadius)
      ((n : ℝ)/(t/16))
      +
    ∫ q in quarticSignedPoleCanonicalLocalRadius..((n : ℝ)/(t/16)),
      compactCosineD5
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t) q
        *
      anchoredPrimitive4
        W.quarticScaleSymmetricWindowDiscrepancy
        quarticSignedPoleCanonicalLocalRadius q := by
  rw [W.normalizedOuterPairedAbelAt_fourfold_ibp ht n hn hA]
  rw [fourfoldIBPBoundary_eq_upper_sub_lower]
  rw [fourfoldIBPLowerBoundary_anchored_eq_zero]
  ring


theorem QuarticFourSignedPolePair.tendsto_abs_upperIBPBoundary_zero
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    {B1 B2 B3 B4 : ℝ}
    (hB1 : 0 <= B1)
    (hB2 : 0 <= B2)
    (hB3 : 0 <= B3)
    (hB4 : 0 <= B4)
    (henv : W.OuterPrimitivePolynomialEnvelope B1 B2 B3 B4) :
    Tendsto
      (fun Q : ℝ =>
        |fourfoldIBPUpperBoundary
          W.normalizedOrdinateCosineD1
          (compactCosineD2
            (quarticFourSignedPoleCombinedProfile
              W.R W.muHalf W.muTwo t))
          (compactCosineD3
            (quarticFourSignedPoleCombinedProfile
              W.R W.muHalf W.muTwo t))
          (compactCosineD4
            (quarticFourSignedPoleCombinedProfile
              W.R W.muHalf W.muTwo t))
          (anchoredPrimitive1
            W.quarticScaleSymmetricWindowDiscrepancy
            quarticSignedPoleCanonicalLocalRadius)
          (anchoredPrimitive2
            W.quarticScaleSymmetricWindowDiscrepancy
            quarticSignedPoleCanonicalLocalRadius)
          (anchoredPrimitive3
            W.quarticScaleSymmetricWindowDiscrepancy
            quarticSignedPoleCanonicalLocalRadius)
          (anchoredPrimitive4
            W.quarticScaleSymmetricWindowDiscrepancy
            quarticSignedPoleCanonicalLocalRadius)
          Q|)
      atTop (𝓝 0) := by
  obtain ⟨K,hK,hbound⟩ :=
    W.exists_upperIBPBoundary_invSq_bound
      hB1 hB2 hB3 hB4 henv
  have hinv :
      Tendsto (fun Q : ℝ => Q⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hsq :
      Tendsto (fun Q : ℝ => (Q⁻¹)^2) atTop (𝓝 0) :=
    hinv.pow 2
  have hg :
      Tendsto (fun Q : ℝ => K / Q^2) atTop (𝓝 0) := by
    have hm := tendsto_const_nhds.mul hsq
    simpa [div_eq_mul_inv, inv_pow] using hm
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun Q => abs_nonneg _
  · filter_upwards [
      eventually_ge_atTop
        (max 1 quarticSignedPoleCanonicalLocalRadius)
    ] with Q hQ
    exact hbound Q hQ
  · exact hg


/-!
## Scalar norm contract for the fifth-derivative interior

After fourfold IBP the only vertical interior is

  integral C_W^(5)(q) * P4_W(q) dq.

We expose the two scalar envelopes needed to bound it:

* B4 bounds the anchored fourth discrepancy primitive;
* K5 bounds the finite outer L1 mass of the fifth cosine derivative.

The resulting product B4*K5 is the complete kernel-side cost.
-/

def QuarticFourSignedPolePair.OuterAnchoredFourthPrimitiveUniformBound
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (B4 : ℝ) : Prop :=
  ∀ q : ℝ,
    quarticSignedPoleCanonicalLocalRadius <= q ->
    |anchoredPrimitive4
      W.quarticScaleSymmetricWindowDiscrepancy
      quarticSignedPoleCanonicalLocalRadius q|
      <= B4

def QuarticFourSignedPolePair.FifthDerivativeOuterL1Envelope
    {t : ℝ}
    (W : QuarticFourSignedPolePair t)
    (K5 : ℝ) : Prop :=
  ∀ Q : ℝ,
    quarticSignedPoleCanonicalLocalRadius <= Q ->
    (∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
      |compactCosineD5
        (quarticFourSignedPoleCombinedProfile
          W.R W.muHalf W.muTwo t) q|)
      <= K5

theorem QuarticFourSignedPolePair.fifthInterior_abs_le_B4_mul_intervalL1
    {t B4 Q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hQ : quarticSignedPoleCanonicalLocalRadius <= Q)
    (hB4nonneg : 0 <= B4)
    (hB4 : W.OuterAnchoredFourthPrimitiveUniformBound B4) :
    |
      ∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
        compactCosineD5
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t) q
          *
        anchoredPrimitive4
          W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius q
    |
      <=
    B4 *
      (∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
        |compactCosineD5
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t) q|) := by
  let P : ℝ -> ℝ :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  let A : ℝ -> ℝ :=
    W.quarticScaleSymmetricWindowDiscrepancy
  let P4 : ℝ -> ℝ :=
    anchoredPrimitive4 A quarticSignedPoleCanonicalLocalRadius
  have hPcont : Continuous P :=
    quarticFourSignedPoleCombinedProfile_continuous W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hC5cont : Continuous (compactCosineD5 P) :=
    compactCosineD5_continuous hPcont hPc
  have hAint :
      IntervalIntegrable A volume
        quarticSignedPoleCanonicalLocalRadius Q :=
    W.quarticScaleSymmetricWindowDiscrepancy_intervalIntegrable
      hQ
  obtain ⟨_h1ac,_h2ac,_h3ac,hP4ac⟩ :=
    anchoredPrimitive_ladder_ac hAint
  have hP4cont :
      ContinuousOn P4
        (Set.uIcc quarticSignedPoleCanonicalLocalRadius Q) :=
    hP4ac.continuousOn
  have hprodI :
      IntervalIntegrable
        (fun q => compactCosineD5 P q * P4 q)
        volume quarticSignedPoleCanonicalLocalRadius Q :=
    (hC5cont.continuousOn.mul hP4cont).intervalIntegrable
  have hC5absI :
      IntervalIntegrable
        (fun q => |compactCosineD5 P q|)
        volume quarticSignedPoleCanonicalLocalRadius Q :=
    hC5cont.abs.intervalIntegrable _ _
  have hmajorI :
      IntervalIntegrable
        (fun q => B4 * |compactCosineD5 P q|)
        volume quarticSignedPoleCanonicalLocalRadius Q :=
    hC5absI.const_mul B4
  calc
    |
      ∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
        compactCosineD5 P q * P4 q
    |
      <=
    ∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
      |compactCosineD5 P q * P4 q| :=
        intervalIntegral.abs_integral_le_integral_abs hQ
    _ <=
    ∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
      B4 * |compactCosineD5 P q| := by
        apply intervalIntegral.integral_mono_on
          hQ hprodI.abs hmajorI
        intro q hq
        rw [abs_mul]
        have hprim : |P4 q| <= B4 := by
          apply hB4 q
          exact (Set.uIcc_of_le hQ ▸ hq).1
        exact mul_le_mul_of_nonneg_left
          hprim (abs_nonneg _)
    _ =
    B4 *
      (∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
        |compactCosineD5 P q|) := by
        rw [intervalIntegral.integral_const_mul]

theorem QuarticFourSignedPolePair.fifthInterior_abs_le_B4_mul_K5
    {t B4 K5 Q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hQ : quarticSignedPoleCanonicalLocalRadius <= Q)
    (hB4nonneg : 0 <= B4)
    (hK5nonneg : 0 <= K5)
    (hB4 : W.OuterAnchoredFourthPrimitiveUniformBound B4)
    (hK5 : W.FifthDerivativeOuterL1Envelope K5) :
    |
      ∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
        compactCosineD5
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t) q
          *
        anchoredPrimitive4
          W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius q
    |
      <= B4 * K5 := by
  have hinner :=
    W.fifthInterior_abs_le_B4_mul_intervalL1
      hQ hB4nonneg hB4
  have hmass := hK5 Q hQ
  exact hinner.trans
    (mul_le_mul_of_nonneg_left hmass hB4nonneg)

theorem QuarticFourSignedPolePair.normalizedOuterPairedAbelAt_abs_le_boundary_add_B4K5
    {t B4 K5 : ℝ}
    (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hB4nonneg : 0 <= B4)
    (hK5nonneg : 0 <= K5)
    (hB4 : W.OuterAnchoredFourthPrimitiveUniformBound B4)
    (hK5 : W.FifthDerivativeOuterL1Envelope K5)
    (n : ℕ)
    (hn :
      quarticSignedPoleCanonicalPhysicalHalfWidth t <= (n : ℝ))
    (hA :
      IntervalIntegrable
        W.quarticScaleSymmetricWindowDiscrepancy
        volume
        quarticSignedPoleCanonicalLocalRadius
        ((n : ℝ)/(t/16))) :
    |W.normalizedOuterPairedAbelAt n|
      <=
    |
      fourfoldIBPUpperBoundary
        W.normalizedOrdinateCosineD1
        (compactCosineD2
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t))
        (compactCosineD3
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t))
        (compactCosineD4
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t))
        (anchoredPrimitive1
          W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius)
        (anchoredPrimitive2
          W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius)
        (anchoredPrimitive3
          W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius)
        (anchoredPrimitive4
          W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius)
        ((n : ℝ)/(t/16))
    |
      + B4*K5 := by
  rw [W.normalizedOuterPairedAbelAt_eq_upperBoundary_add_fifthInterior
    ht n hn hA]
  have hQ :
      quarticSignedPoleCanonicalLocalRadius
        <= (n : ℝ)/(t/16) := by
    rw [le_div_iff₀ (by positivity : 0 < t/16)]
    exact hn
  have hinter :=
    W.fifthInterior_abs_le_B4_mul_K5
      hQ hB4nonneg hK5nonneg hB4 hK5
  exact (abs_add _ _).trans (add_le_add_left hinter _)


def QuarticFourSignedPolePair.fifthDerivativeGlobalL1Mass
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) : ℝ :=
  ∫ q : ℝ,
    |compactCosineD5
      (quarticFourSignedPoleCombinedProfile
        W.R W.muHalf W.muTwo t) q|

theorem QuarticFourSignedPolePair.fifthDerivativeGlobalL1Mass_nonneg
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    0 <= W.fifthDerivativeGlobalL1Mass := by
  unfold QuarticFourSignedPolePair.fifthDerivativeGlobalL1Mass
  positivity

theorem QuarticFourSignedPolePair.fifthDerivativeOuterL1Envelope_global
    {t : ℝ}
    (W : QuarticFourSignedPolePair t) :
    W.FifthDerivativeOuterL1Envelope
      W.fifthDerivativeGlobalL1Mass := by
  intro Q hQ
  let P : ℝ -> ℝ :=
    quarticFourSignedPoleCombinedProfile
      W.R W.muHalf W.muTwo t
  have hP2 :
      ContDiff ℝ 2 P :=
    quarticFourSignedPoleCombinedProfile_contDiff_two W.Rpos
  have hPc : HasCompactSupport P :=
    quarticFourSignedPoleCombinedProfile_compact W.Rpos
  have hC5 : Integrable (compactCosineD5 P) :=
    compactCosineD5_integrable hP2 hPc
  have hC5abs : Integrable (fun q : ℝ => |compactCosineD5 P q|) :=
    hC5.abs
  unfold QuarticFourSignedPolePair.fifthDerivativeGlobalL1Mass
  dsimp [P] at hC5abs ⊢
  rw [intervalIntegral.integral_of_le hQ]
  apply setIntegral_mono_set
  · exact hC5abs.integrableOn
  · filter_upwards with q
    exact abs_nonneg _
  · exact Filter.Eventually.of_forall fun q hq =>
      Set.mem_univ q

theorem QuarticFourSignedPolePair.fifthInterior_abs_le_primitive_mul_globalL1
    {t B4 Q : ℝ}
    (W : QuarticFourSignedPolePair t)
    (hQ : quarticSignedPoleCanonicalLocalRadius <= Q)
    (hB4nonneg : 0 <= B4)
    (hB4 : W.OuterAnchoredFourthPrimitiveUniformBound B4) :
    |
      ∫ q in quarticSignedPoleCanonicalLocalRadius..Q,
        compactCosineD5
          (quarticFourSignedPoleCombinedProfile
            W.R W.muHalf W.muTwo t) q
          *
        anchoredPrimitive4
          W.quarticScaleSymmetricWindowDiscrepancy
          quarticSignedPoleCanonicalLocalRadius q
    |
      <= B4 * W.fifthDerivativeGlobalL1Mass := by
  exact
    W.fifthInterior_abs_le_B4_mul_K5
      hQ hB4nonneg
      W.fifthDerivativeGlobalL1Mass_nonneg
      hB4
      W.fifthDerivativeOuterL1Envelope_global

end Synthesis
