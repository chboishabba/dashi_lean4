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

end Synthesis
