import Synthesis.RiemannGammaCenteredQuadraticEnvelope
import Synthesis.RiemannFinalEvenConeNearFarSplit

/-!
# Final-carrier centered Off + Gamma quadratic correction

The final universal even-cone Off channel has the same radius-centering identity
as Gamma.  For h_r(u)=g(u)(cos(r u)-1),

  D_off(g,t,r) - D_off(g,t,0) = D_off(h_r,t,0).

The existing literal off-ordinate envelope applied to h_r, together with the
quadratic centered strip theorem, therefore yields an O(r^2) bound directly on
the final pole-quotient response.

Combining it with the centered Gamma correction keeps Off and Gamma on the same
literal taper and avoids the projective response/balance firewall.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilEvenChannelTaper
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilOffOrdinateTail
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.LiteralWeilOffOrdinateEvenConeReflectionSymmetrization

theorem finalPairTerm_centered_radius {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (t r : ℝ) (sigma : ((SameOrd t)ᶜ : Set Zeros)) :
    finalPairTerm g t r sigma - finalPairTerm g t 0 sigma
      = finalPairTerm (gammaCenteredTaper g r) t 0 sigma := by
  let rho : Zeros := (sigma : Zeros)
  have hr :=
    zeroConeValue_add_reflect_eq_integral hgs.continuous hgc heven t r rho
  have h0 :=
    zeroConeValue_add_reflect_eq_integral hgs.continuous hgc heven t 0 rho
  have hc2 := gammaCenteredTaper_contDiff hgs r
  have hcc := gammaCenteredTaper_hasCompactSupport hgc r
  have hce := gammaCenteredTaper_even heven r
  have hc :=
    zeroConeValue_add_reflect_eq_integral hc2.continuous hcc hce t 0 rho
  have hreflect :
      ((reflectOffOrdEquiv t sigma : ((SameOrd t)ᶜ : Set Zeros)) : Zeros)
        = reflectZero rho := rfl
  unfold finalPairTerm
  rw [hreflect, hr, h0, hc]
  simp only [zero_mul, Real.cos_zero, mul_one]
  ring_nf
  congr 2
  apply integral_congr_ae
  filter_upwards with u
  unfold reflectionPairWeight gammaCenteredTaper
  ring

theorem finalOffOrd_centered_radius {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    evenConeFunctional (offOrdVec (sampleFam g t r) t)
      - evenConeFunctional (offOrdVec (sampleFam g t 0) t)
      =
    evenConeFunctional
      (offOrdVec (sampleFam (gammaCenteredTaper g r) t 0) t) := by
  have hsumr := summable_finalPairTerm hgs hgc t r
  have hsum0 := summable_finalPairTerm hgs hgc t 0
  have hc2 := gammaCenteredTaper_contDiff hgs r
  have hcc := gammaCenteredTaper_hasCompactSupport hgc r
  have hsumc := summable_finalPairTerm hc2 hcc t 0
  rw [finalOffOrd_eq_half_pair_tsum hgs hgc t r,
      finalOffOrd_eq_half_pair_tsum hgs hgc t 0,
      finalOffOrd_eq_half_pair_tsum hc2 hcc t 0]
  rw [← mul_sub, ← hsumr.tsum_sub hsum0]
  congr 1
  exact tsum_congr (fun sigma =>
    finalPairTerm_centered_radius hgs hgc heven t r sigma)

theorem abs_finalOffOrd_centered_le {g : ℝ → ℝ} {Λ : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    (hΛ : 0 ≤ Λ) (t r : ℝ) :
    |evenConeFunctional (offOrdVec (sampleFam g t r) t)
      - evenConeFunctional (offOrdVec (sampleFam g t 0) t)|
      ≤ 2 * r ^ 2 * gammaCenteredStripCoeff g Λ t * offOrdWeight t := by
  have hgc :=
    Zeta23Bridge.LiteralWeilProjectiveStripConstant.hasCompactSupport_of_radius hsupp
  have hc2 := gammaCenteredTaper_contDiff hgs r
  have hcc := gammaCenteredTaper_hasCompactSupport hgc r
  have hcs : ∀ u, gammaCenteredTaper g r u ≠ 0 → |u| ≤ Λ := by
    intro u hu
    apply hsupp u
    intro hg
    apply hu
    simp [gammaCenteredTaper, hg]
  have henv :=
    offOrdinateConeEnvelope hc2 hcc hcs hΛ t 0
  have hstrip := stripConst_gammaCentered_le hgs hsupp hΛ t r
  have hw := offOrdWeight_nonneg t
  rw [finalOffOrd_centered_radius hgs hgc heven t r]
  unfold epsZero at henv
  have hsame :
      stripConst (sampleTest (gammaCenteredTaper g r) t (-0)) Λ
        = stripConst (sampleTest (gammaCenteredTaper g r) t 0) Λ := by simp
  rw [hsame] at henv
  have hmul :
      4 * stripConst (sampleTest (gammaCenteredTaper g r) t 0) Λ * offOrdWeight t
        ≤ 4 * (r ^ 2 * gammaCenteredStripCoeff g Λ t) * offOrdWeight t := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hstrip (by norm_num))
      hw
  nlinarith

theorem exists_finalComplementCenteredQuadraticEnvelope :
    ∃ CG : ℝ, 0 ≤ CG ∧
      ∀ {g : ℝ → ℝ} {Λ : ℝ},
        ContDiff ℝ 2 g →
        (∀ u, g (-u) = g u) →
        (∀ u, g u ≠ 0 → |u| ≤ Λ) →
        0 ≤ Λ →
        ∀ t r : ℝ,
          |(evenConeFunctional (offOrdVec (sampleFam g t r) t)
              - evenConeFunctional (offOrdVec (sampleFam g t 0) t))
            + ((gammaResp g t r + gammaResp g t (-r))
                - 2 * gammaResp g t 0)|
          ≤ r ^ 2 *
            (4 * gammaCenteredStripCoeff g Λ t * offOrdWeight t
              + 2 * CG * gammaCenteredStripCoeff g Λ t) := by
  obtain ⟨CG, hCG, hGamma⟩ := exists_centeredGammaQuadraticEnvelope
  refine ⟨CG, hCG, ?_⟩
  intro g Λ hgs heven hsupp hΛ t r
  have hOff := abs_finalOffOrd_centered_le hgs heven hsupp hΛ t r
  have hgc :=
    Zeta23Bridge.LiteralWeilProjectiveStripConstant.hasCompactSupport_of_radius hsupp
  have hGammaId :=
    gammaResp_centered_radius hgs hgc heven hsupp hΛ t r
  have hGammaBound := hGamma hgs heven hsupp hΛ t r
  have hGammaCorr :
      |(gammaResp g t r + gammaResp g t (-r))
          - 2 * gammaResp g t 0|
        ≤ 2 * r ^ 2 * (CG * gammaCenteredStripCoeff g Λ t) := by
    rw [hGammaId, abs_mul, show |(2 : ℝ)| = 2 by norm_num]
    nlinarith
  have htri := abs_add_le
    (evenConeFunctional (offOrdVec (sampleFam g t r) t)
      - evenConeFunctional (offOrdVec (sampleFam g t 0) t))
    ((gammaResp g t r + gammaResp g t (-r))
      - 2 * gammaResp g t 0)
  nlinarith [htri, hOff, hGammaCorr]

end Synthesis
