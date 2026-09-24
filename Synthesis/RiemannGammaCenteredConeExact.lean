import Zeta23Bridge.LiteralWeilGammaProjectiveBound

/-!
# Centered Gamma cone identity on the literal pole-quotient taper

The existing radiuswise Gamma estimate takes absolute values of the two samples
separately and pays the shrinking-support second-derivative norm.  Before doing
that, the literal cone value admits an exact centered decomposition.

For

    h_r(u) = g(u) (cos(r u) - 1),

the two-sample transform satisfies

    ĝ(y+r) + ĝ(y-r) - 2 ĝ(y) = 2 ĥ_r(y),

hence the Gamma responses satisfy

    Γ_g(t,r) + Γ_g(t,-r) - 2 Γ_g(t,0) = 2 Γ_{h_r}(t,0).

Combining this with gammaConeValue_exact gives

    ℓ(Q_Γ(g,t,r))
      = -2 Γ_g(t,0) - 2 Γ_{h_r}(t,0).

This is an exact identity on the literal two-sample cone.  It does not import
the rank-two/projective balance and therefore does not cross the projective
WrongType firewall.

The analytic opportunity is that the dangerous g'' term in h_r'' is multiplied
by cos(r u)-1 = O(r²u²), so a support radius Λ can cancel the usual Λ⁻²
derivative growth instead of paying it naked.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilEvenChannelTaper
open Zeta23Bridge.LiteralWeilGammaChannel
open Zeta23Bridge.LiteralWeilGammaConeBound
open Zeta23Bridge.LiteralWeilGammaProjectiveBound

/-- The centered radius defect taper. -/
def gammaCenteredTaper (g : ℝ → ℝ) (r : ℝ) : ℝ → ℝ :=
  fun u => g u * (Real.cos (r * u) - 1)

theorem gammaCenteredTaper_continuous {g : ℝ → ℝ} (hg : Continuous g) (r : ℝ) :
    Continuous (gammaCenteredTaper g r) := by
  unfold gammaCenteredTaper
  fun_prop

theorem gammaCenteredTaper_contDiff {g : ℝ → ℝ}
    (hgs : ContDiff ℝ 2 g) (r : ℝ) :
    ContDiff ℝ 2 (gammaCenteredTaper g r) := by
  unfold gammaCenteredTaper
  fun_prop

theorem gammaCenteredTaper_hasCompactSupport {g : ℝ → ℝ}
    (hgc : HasCompactSupport g) (r : ℝ) :
    HasCompactSupport (gammaCenteredTaper g r) := by
  unfold gammaCenteredTaper
  exact hgc.mul_right

theorem gammaCenteredTaper_even {g : ℝ → ℝ}
    (heven : ∀ u, g (-u) = g u) (r : ℝ) :
    ∀ u, gammaCenteredTaper g r (-u) = gammaCenteredTaper g r u := by
  intro u
  unfold gammaCenteredTaper
  rw [heven, neg_mul, Real.cos_neg]

/-- Frequency-level centering identity. -/
theorem cosFT_centered_radius {g : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (y r : ℝ) :
    cosFT g (y + r) + cosFT g (y - r) - 2 * cosFT g y
      = 2 * cosFT (gammaCenteredTaper g r) y := by
  have hcone := cosFT_cone hg hgc y r
  have h0 := cosFT_cone hg hgc y 0
  have hc : Continuous (fun u : ℝ => coneWeight g y u * Real.cos (r * u)) := by
    unfold coneWeight
    fun_prop
  have hcc : HasCompactSupport (fun u : ℝ => coneWeight g y u * Real.cos (r * u)) := by
    exact (coneWeight_hasCompactSupport hgc y).mul_right
  have hbase : Continuous (fun u : ℝ => coneWeight g y u) := coneWeight_continuous hg y
  have hbasec : HasCompactSupport (coneWeight g y) := coneWeight_hasCompactSupport hgc y
  have hi1 : Integrable (fun u : ℝ => coneWeight g y u * Real.cos (r * u)) :=
    hc.integrable_of_hasCompactSupport hcc
  have hi0 : Integrable (coneWeight g y) :=
    hbase.integrable_of_hasCompactSupport hbasec
  have hdiff :
      (∫ u : ℝ, coneWeight g y u * Real.cos (r * u))
        - (∫ u : ℝ, coneWeight g y u)
      = ∫ u : ℝ, 2 * (gammaCenteredTaper g r u * Real.cos (y * u)) := by
    rw [← integral_sub hi1 hi0]
    congr 1
    funext u
    unfold coneWeight gammaCenteredTaper
    ring
  rw [show cosFT g (y + 0) + cosFT g (y - 0) = 2 * cosFT g y by ring] at h0
  calc
    cosFT g (y + r) + cosFT g (y - r) - 2 * cosFT g y
        = (∫ u : ℝ, coneWeight g y u * Real.cos (r * u))
          - (∫ u : ℝ, coneWeight g y u) := by
            rw [hcone]
            linarith [h0]
    _ = ∫ u : ℝ, 2 * (gammaCenteredTaper g r u * Real.cos (y * u)) := hdiff
    _ = 2 * cosFT (gammaCenteredTaper g r) y := by
      rw [integral_const_mul]
      rfl

/-- Pointwise centered identity for the Gamma integrand. -/
theorem gammaIntegrand_centered_radius {g : ℝ → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (t r x : ℝ) :
    gammaIntegrand g t r x + gammaIntegrand g t (-r) x
        - 2 * gammaIntegrand g t 0 x
      = 2 * gammaIntegrand (gammaCenteredTaper g r) t 0 x := by
  have hft := cosFT_centered_radius hg hgc (x - t) r
  unfold gammaIntegrand
  rw [show x + r - t = x - t + r by ring,
      show x + -r - t = x - t - r by ring,
      show x + 0 - t = x - t by ring]
  linear_combination Zeta23.EF.gammaBracket x * hft

/-- Exact centered identity for the Gamma response. -/
theorem gammaResp_centered_radius {g : ℝ → ℝ} {Λ : ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ)
    (t r : ℝ) :
    gammaResp g t r + gammaResp g t (-r) - 2 * gammaResp g t 0
      = 2 * gammaResp (gammaCenteredTaper g r) t 0 := by
  have hcgc : HasCompactSupport (gammaCenteredTaper g r) :=
    gammaCenteredTaper_hasCompactSupport hgc r
  have hceven : ∀ u, gammaCenteredTaper g r (-u) = gammaCenteredTaper g r u :=
    gammaCenteredTaper_even heven r
  have hcsupp : ∀ u, gammaCenteredTaper g r u ≠ 0 → |u| ≤ Λ := by
    intro u hu
    apply hsupp u
    intro hgu
    apply hu
    simp [gammaCenteredTaper, hgu]
  have i1 := integrable_gammaIntegrand hgs hgc heven hsupp hΛ t r
  have i2 := integrable_gammaIntegrand hgs hgc heven hsupp hΛ t (-r)
  have i0 := integrable_gammaIntegrand hgs hgc heven hsupp hΛ t 0
  have hcenterC2 := gammaCenteredTaper_contDiff hgs r
  have ic := integrable_gammaIntegrand hcenterC2 hcgc hceven hcsupp hΛ t 0
  unfold gammaResp
  have hpt : ∀ x : ℝ,
      gammaIntegrand g t r x + gammaIntegrand g t (-r) x
          - 2 * gammaIntegrand g t 0 x
        = 2 * gammaIntegrand (gammaCenteredTaper g r) t 0 x :=
    gammaIntegrand_centered_radius hgs.continuous hgc t r
  have hcong :
      (∫ x : ℝ, (gammaIntegrand g t r x + gammaIntegrand g t (-r) x
          - 2 * gammaIntegrand g t 0 x))
        = ∫ x : ℝ, 2 * gammaIntegrand (gammaCenteredTaper g r) t 0 x :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [integral_sub (i1.add i2) (i0.const_mul 2),
      integral_add i1 i2,
      integral_const_mul,
      hcong,
      integral_const_mul]
  ring

/-- The literal Gamma cone is its radius-zero baseline plus a centered defect. -/
theorem gammaConeValue_centered_exact {g : ℝ → ℝ} {Λ : ℝ}
    (hgs : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ)
    (t r : ℝ) :
    evenConeFunctional (gammaVec (sampleFam g t r))
      = -2 * gammaResp g t 0
        - 2 * gammaResp (gammaCenteredTaper g r) t 0 := by
  have hcone := gammaConeValue_exact hgs.continuous hgc heven t r
  have hcenter :=
    gammaResp_centered_radius hgs hgc heven hsupp hΛ t r
  rw [hcone]
  linarith

end Synthesis
