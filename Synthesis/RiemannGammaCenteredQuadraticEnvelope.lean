import Synthesis.RiemannGammaCenteredQuadraticStrip
import Zeta23Bridge.PoleQuotientGammaBudget

/-!
# Quadratic envelope for the centered literal Gamma defect

Combining the exact centered cone identity with the quadratic strip constant
gives a same-taper, final-carrier estimate for the centered Gamma correction.

There exists an absolute gamma-tail constant CG such that

  |gammaResp(h_r,t,0)|
    <= CG * stripConst(sampleTest h_r t 0, Lambda)
    <= r^2 * CG * gammaCenteredStripCoeff(g,Lambda,t).

Thus the correction

  Gamma_g(t,r)+Gamma_g(t,-r)-2 Gamma_g(t,0)

is O(r^2) without paying the raw shrinking-support second derivative norm.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilGammaConeBound
open Zeta23Bridge.PoleQuotientGammaBudget

theorem exists_centeredGammaQuadraticEnvelope :
    ∃ CG : ℝ, 0 ≤ CG ∧
      ∀ {g : ℝ → ℝ} {Λ : ℝ},
        ContDiff ℝ 2 g →
        (∀ u, g (-u) = g u) →
        (∀ u, g u ≠ 0 → |u| ≤ Λ) →
        0 ≤ Λ →
        ∀ t r : ℝ,
          |gammaResp (gammaCenteredTaper g r) t 0|
            ≤ r ^ 2 * (CG * gammaCenteredStripCoeff g Λ t) := by
  obtain ⟨A, B, hA, hB, hAB⟩ := exists_gammaBracket_bound
  let CG : ℝ := (1 / (2 * π)) * gammaTailConstant A B
  have hCG : 0 ≤ CG := by
    unfold CG
    positivity
  refine ⟨CG, hCG, ?_⟩
  intro g Λ hgs heven hsupp hΛ t r
  let h := gammaCenteredTaper g r
  have hh : ContDiff ℝ 2 h := gammaCenteredTaper_contDiff hgs r
  have hhc : HasCompactSupport h :=
    gammaCenteredTaper_hasCompactSupport
      (Zeta23Bridge.LiteralWeilProjectiveStripConstant.hasCompactSupport_of_radius hsupp) r
  have hheven : ∀ u, h (-u) = h u := gammaCenteredTaper_even heven r
  have hhsupp : ∀ u, h u ≠ 0 → |u| ≤ Λ := by
    intro u hu
    apply hsupp u
    intro hg
    apply hu
    simp [h, gammaCenteredTaper, hg]
  have hInt :=
    integral_abs_gammaIntegrand_le hh hhc hheven hhsupp hΛ t 0 hA hB hAB
  have hResp := abs_gammaResp_le h t 0
  have hStrip := stripConst_gammaCentered_le hgs hsupp hΛ t r
  have hTail : 0 ≤ gammaTailConstant A B :=
    gammaTailConstant_nonneg hA hB
  have hS0 : 0 ≤ stripConst (sampleTest h t 0) Λ :=
    Zeta23Bridge.LiteralWeilOffOrdinateTail.stripConst_nonneg _ _
  have hstep :
      |gammaResp h t 0|
        ≤ CG * stripConst (sampleTest h t 0) Λ := by
    unfold CG at *
    have hpi : 0 < (1 / (2 * π) : ℝ) := by positivity
    calc
      |gammaResp h t 0|
          ≤ (1 / (2 * π)) * ∫ x : ℝ, |gammaIntegrand h t 0 x| := hResp
      _ ≤ (1 / (2 * π)) *
          (stripConst (sampleTest h t 0) Λ * gammaTailConstant A B) :=
        mul_le_mul_of_nonneg_left hInt hpi.le
      _ = ((1 / (2 * π)) * gammaTailConstant A B)
          * stripConst (sampleTest h t 0) Λ := by ring
  have hmul :
      CG * stripConst (sampleTest h t 0) Λ
        ≤ CG * (r ^ 2 * gammaCenteredStripCoeff g Λ t) :=
    mul_le_mul_of_nonneg_left hStrip hCG
  calc
    |gammaResp h t 0|
        ≤ CG * stripConst (sampleTest h t 0) Λ := hstep
    _ ≤ CG * (r ^ 2 * gammaCenteredStripCoeff g Λ t) := hmul
    _ = r ^ 2 * (CG * gammaCenteredStripCoeff g Λ t) := by ring

theorem exists_centeredGammaConeCorrectionQuadratic :
    ∃ CG : ℝ, 0 ≤ CG ∧
      ∀ {g : ℝ → ℝ} {Λ : ℝ},
        ContDiff ℝ 2 g →
        HasCompactSupport g →
        (∀ u, g (-u) = g u) →
        (∀ u, g u ≠ 0 → |u| ≤ Λ) →
        0 ≤ Λ →
        ∀ t r : ℝ,
          |(gammaResp g t r + gammaResp g t (-r))
              - 2 * gammaResp g t 0|
            ≤ 2 * r ^ 2 * (CG * gammaCenteredStripCoeff g Λ t) := by
  obtain ⟨CG, hCG, henv⟩ := exists_centeredGammaQuadraticEnvelope
  refine ⟨CG, hCG, ?_⟩
  intro g Λ hgs hgc heven hsupp hΛ t r
  have hid := gammaResp_centered_radius hgs hgc heven hsupp hΛ t r
  have hb := henv hgs heven hsupp hΛ t r
  rw [hid, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
  nlinarith

end Synthesis
