import Synthesis.RiemannFinalLiteralComplementCenteredQuadratic

/-!
# Exact centering of the literal final complement

For the actual literal final complement

    S_g(t,r) = Off_g(t,r) + Q_Gamma,g(t,r),

and the centered taper

    h_r(u) = g(u) (cos(r u) - 1),

the radius variation is not merely bounded by the h_r response: it IS exactly
that response at radius zero,

    S_g(t,r) - S_g(t,0) = S_{h_r}(t,0).

For a nonnegative taper g, h_r <= 0 pointwise.  Consequently the prize-facing
problem after the magnitude estimates is the sign of one explicit centered
literal complement.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23 Zeta23.EF
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilGammaConeBound
open Zeta23Bridge.LiteralWeilProjectiveStripConstant

theorem finalLiteralComplement_centered_exact {g : ℝ → ℝ} {Λ : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    (hΛ : 0 ≤ Λ)
    (t r : ℝ) :
    finalLiteralComplement g t r - finalLiteralComplement g t 0
      = finalLiteralComplement (gammaCenteredTaper g r) t 0 := by
  have hOff := finalOffOrd_centered_radius hgs hgc heven t r
  have hGamma :=
    gammaCone_centered_radius hgs hgc heven hsupp hΛ t r
  have hc2 := gammaCenteredTaper_contDiff hgs r
  have hcc := gammaCenteredTaper_hasCompactSupport hgc r
  have hce := gammaCenteredTaper_even heven r
  have hGammaCentered :=
    gammaConeValue_exact hc2.continuous hcc hce t 0
  unfold finalLiteralComplement
  rw [hOff, hGamma]
  rw [hGammaCentered]
  simp only [neg_zero]
  ring

theorem gammaCenteredTaper_nonpos {g : ℝ → ℝ}
    (hnn : ∀ u, 0 ≤ g u) (r u : ℝ) :
    gammaCenteredTaper g r u ≤ 0 := by
  unfold gammaCenteredTaper
  have hc : Real.cos (r * u) - 1 ≤ 0 := by
    linarith [Real.cos_le_one (r * u)]
  exact mul_nonpos_of_nonneg_of_nonpos (hnn u) hc

def positiveCenteredTaper (g : ℝ → ℝ) (r : ℝ) : ℝ → ℝ :=
  fun u => g u * (1 - Real.cos (r * u))

theorem positiveCenteredTaper_nonneg {g : ℝ → ℝ}
    (hnn : ∀ u, 0 ≤ g u) (r u : ℝ) :
    0 ≤ positiveCenteredTaper g r u := by
  unfold positiveCenteredTaper
  have hc : 0 ≤ 1 - Real.cos (r * u) := by
    linarith [Real.cos_le_one (r * u)]
  exact mul_nonneg (hnn u) hc

theorem gammaCenteredTaper_eq_neg_positiveCenteredTaper
    (g : ℝ → ℝ) (r : ℝ) :
    gammaCenteredTaper g r = fun u => - positiveCenteredTaper g r u := by
  funext u
  unfold gammaCenteredTaper positiveCenteredTaper
  ring

/--
The exact remaining sign leaf.

Any direct proof that the centered literal complement is nonpositive immediately
shows that increasing from radius zero to the selected radius does not increase
the literal signed complement.
-/
theorem finalLiteralComplement_le_radiusZero_of_centered_nonpos
    {g : ℝ → ℝ} {Λ : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ)
    (hΛ : 0 ≤ Λ)
    (t r : ℝ)
    (hsign : finalLiteralComplement (gammaCenteredTaper g r) t 0 ≤ 0) :
    finalLiteralComplement g t r ≤ finalLiteralComplement g t 0 := by
  rw [← sub_nonpos]
  rw [finalLiteralComplement_centered_exact hgs hgc heven hsupp hΛ t r]
  exact hsign

end Synthesis
