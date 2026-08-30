/-
# An explicit envelope for the residual channels in the two-radius geometry

`LiteralWeilTwoRadiusBalance.twoRadiusResidualBalance` is the exact identity

    D_cluster(t, r) = R(2r) A_0(r) - R(r) A_0(2r),
    R(s) = ℓ(Q_offOrd) + ℓ(Q_prime) + ℓ(Q_Γ) + ℓ(Q_pole)   at sampling radius s.

This module bounds the right-hand side explicitly, at *both* radii, from the
envelopes already proved:

* `epsZero`  — the off-ordinate zero tail (`LiteralWeilOffOrdinateTail`),
* `epsGamma` — the gamma bracket (`LiteralWeilGammaConeBound`),
* the pole channel, whose cone value is the *exact* number `-4 P_t(s)` with
  `P_t(s) = poleEvenResp g t s`; the taper kills it at the base radius `r` only, so
  the doubled radius carries `4 |P_t(2r)|` explicitly,
* the prime channel, which vanishes identically for the high-ordinate tapers
  (`LiteralWeilPrimeEvenCone`).

The capstone `clusterHeightDefectBoundedByResidualEnvelope` is therefore

    0 < D_cluster(t, r)
        ≤ ε(2r) |A_0(r)| + ε(r) |A_0(2r)|,
    ε(s) = ε_zero(g, Λ, t, s) + ε_Γ(g, t, s) + 4 |P_t(s)|,

for an actual off-line zero at a high nonzero ordinate.  Every quantity on the
right is an explicit finite integral expression.  **No claim is made that the right
side is smaller than the left**; that inequality is precisely the remaining
obligation recorded in `FRONTIER.md`.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilTwoRadiusBalance
import Zeta23Bridge.LiteralWeilGammaConeBound
import Zeta23Bridge.LiteralWeilPrimeEvenCone

noncomputable section

open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilTwoRadiusResidualEnvelope

open Zeta23Bridge.LiteralWeilParityBalance Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilEvenChannelTaper Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilTwoRadiusBalance
open Zeta23Bridge.LiteralWeilOffOrdinateTail Zeta23Bridge.LiteralWeilGammaConeBound
open Zeta23Bridge.LiteralWeilPrimeEvenCone

/-- **The exact pole cone value.**  The even cone functional reads the pole channel
at sampling radius `s` as `-4 P_t(s)`. -/
theorem poleCone_value {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t s : ℝ) :
    evenConeFunctional (poleVec (sampleFam g t s)) = -4 * poleEvenResp g t s := by
  rw [poleVec_sampleFam hg hgc heven, map_smul, poleParityVec, map_add,
    evenConeFunctional_evenPattern, evenConeFunctional_oddPattern]
  simp only [smul_eq_mul, add_zero]
  ring

/-- The explicit residual envelope at one sampling radius. -/
def epsResidual (g : ℝ → ℝ) (Λ t s : ℝ) : ℝ :=
  epsZero g Λ t s + epsGamma g t s + 4 * |poleEvenResp g t s|

/-- **`abs_residualCone_le`.**  With the prime channel absent, the total residual
cone value at sampling radius `s` obeys the explicit envelope. -/
theorem abs_residualCone_le {g : ℝ → ℝ} {Λ : ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ)
    (hshort : ∀ u, g u ≠ 0 → |u| < Real.log 2) (t s : ℝ) :
    |residualCone g t s| ≤ epsResidual g Λ t s := by
  have hoff := offOrdinateConeEnvelope hgs hgc hsupp hΛ t s
  have hgam := gammaConeEnvelope hgs.continuous hgc heven t s
  have hprime := primeConeValue_eq_zero_of_short_taper hshort t s
  have hpole := poleCone_value hgs.continuous hgc heven t s
  have hpoleabs : |evenConeFunctional (poleVec (sampleFam g t s))| = 4 * |poleEvenResp g t s| := by
    rw [hpole, abs_mul]
    norm_num
  unfold residualCone epsResidual
  rw [hprime, add_zero]
  calc |evenConeFunctional (offOrdVec (sampleFam g t s) t)
          + evenConeFunctional (gammaVec (sampleFam g t s))
          + evenConeFunctional (poleVec (sampleFam g t s))|
      ≤ |evenConeFunctional (offOrdVec (sampleFam g t s) t)
          + evenConeFunctional (gammaVec (sampleFam g t s))|
        + |evenConeFunctional (poleVec (sampleFam g t s))| := abs_add_le _ _
    _ ≤ (|evenConeFunctional (offOrdVec (sampleFam g t s) t)|
          + |evenConeFunctional (gammaVec (sampleFam g t s))|)
        + |evenConeFunctional (poleVec (sampleFam g t s))| := by
          gcongr
          exact abs_add_le _ _
    _ ≤ epsZero g Λ t s + epsGamma g t s + 4 * |poleEvenResp g t s| := by
          rw [hpoleabs]; linarith

/-- **`twoRadiusResidualEnvelope`.**  The two-radius residual determinant obeys the
explicit envelope built from the two single-radius envelopes. -/
theorem twoRadiusResidualEnvelope {g : ℝ → ℝ} {Λ : ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 → |u| ≤ Λ) (hΛ : 0 ≤ Λ)
    (hshort : ∀ u, g u ≠ 0 → |u| < Real.log 2) (t r : ℝ) :
    |residualCone g t (2 * r) * evenResp g 0 r - residualCone g t r * evenResp g 0 (2 * r)|
      ≤ epsResidual g Λ t (2 * r) * |evenResp g 0 r|
        + epsResidual g Λ t r * |evenResp g 0 (2 * r)| := by
  have h1 := abs_residualCone_le hgs hgc heven hsupp hΛ hshort t (2 * r)
  have h2 := abs_residualCone_le hgs hgc heven hsupp hΛ hshort t r
  calc |residualCone g t (2 * r) * evenResp g 0 r - residualCone g t r * evenResp g 0 (2 * r)|
      ≤ |residualCone g t (2 * r) * evenResp g 0 r|
        + |residualCone g t r * evenResp g 0 (2 * r)| := abs_sub _ _
    _ = |residualCone g t (2 * r)| * |evenResp g 0 r|
        + |residualCone g t r| * |evenResp g 0 (2 * r)| := by rw [abs_mul, abs_mul]
    _ ≤ epsResidual g Λ t (2 * r) * |evenResp g 0 r|
        + epsResidual g Λ t r * |evenResp g 0 (2 * r)| :=
          add_le_add (mul_le_mul_of_nonneg_right h1 (abs_nonneg _))
            (mul_le_mul_of_nonneg_right h2 (abs_nonneg _))

/-- **`clusterHeightDefectBoundedByResidualEnvelope`.**  For an actual off-line
nontrivial zero of `riemannZeta` at a nonzero ordinate high enough that the literal
prime frequencies miss the taper support, the strictly positive cluster height
defect is bounded by a completely explicit residual envelope:

    0 < D_cluster(t, r) ≤ ε(2r) |A_0(r)| + ε(r) |A_0(2r)|.

The remaining obligation is exactly to make the right-hand side smaller than the
left; nothing here asserts that it is. -/
theorem clusterHeightDefectBoundedByResidualEnvelope {ρstar : Zeros} {t : ℝ}
    (him : (ρstar : ℂ).im = t) (hoffline : heightOf ρstar ≠ 0) (ht : t ≠ 0)
    (hheight : 9 * π ≤ 4 * |t| * Real.log 2) :
    ∃ (g : ℝ → ℝ) (r Λ : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r ∧ 0 ≤ Λ ∧ (∀ u, g u ≠ 0 → |u| ≤ Λ) ∧ poleEvenResp g t r = 0
      ∧ evenConeFunctional (primeVec (sampleFam g t r)) = 0
      ∧ 0 < clusterHeightDefect g t r
      ∧ clusterHeightDefect g t r
          ≤ epsResidual g Λ t (2 * r) * |evenResp g 0 r|
            + epsResidual g Λ t r * |evenResp g 0 (2 * r)| := by
  obtain ⟨g, r, hgs, hgc, heven, hr, hnn, hrad, ⟨u₀, v₀, hu₀, hv₀, hne⟩, hpole, -, hsupp9⟩ :=
    exists_positive_taper_poleEven_zero ht
  obtain ⟨Λ, hΛ, hsupp⟩ := exists_support_radius hgc
  have hshort : ∀ u, g u ≠ 0 → |u| < Real.log 2 := short_taper_of_height hsupp9 ht hheight
  have hpos : 0 < clusterHeightDefect g t r :=
    literalClusterTwoRadiusDetectsOffLine hgs hgc heven hnn hr hrad hu₀ hv₀ hne
      ⟨ρstar, him⟩ hoffline
  have hbal := twoRadiusResidualBalance hgs hgc heven t r
  have henv := twoRadiusResidualEnvelope hgs hgc heven hsupp hΛ hshort t r
  refine ⟨g, r, Λ, hgs, hgc, heven, hr, hΛ, hsupp, hpole,
    primeConeValue_eq_zero_of_short_taper hshort t r, hpos, ?_⟩
  have hle := (abs_le.mp henv).2
  rw [hbal]
  linarith

end LiteralWeilTwoRadiusResidualEnvelope
end Zeta23Bridge
