/-
# The literal Weil balance in the two-radius even geometry

`LiteralWeilSameOrdinateEvenCone.literalWeilOrdinateFibreBalance` is the literal
balance split along the ordinate fibre,

    Q_cluster + Q_offOrd + Q_prime + Q_Γ + Q_pole = 0,

read at a single sampling radius.  `LiteralWeilClusterTwoRadiusProfile` showed that
the *pair* of even cone values at the radii `r` and `2r` — the cluster's two-radius
profile — is what actually sees the heights of the fibre.

This module reads the literal balance at **both** radii and combines the two
readings into the same determinant.  Writing

    R(s) = ℓ(Q_offOrd) + ℓ(Q_prime) + ℓ(Q_Γ) + ℓ(Q_pole)   at sampling radius s,

the balance gives `Σ_ρ coneWeight(s, ρ) = -R(s)` for every `s`, and hence the exact
identity

    D_cluster(t, r) = -( R(r) A_0(2r) - R(2r) A_0(r) ).                (†)

`(†)` is an equality, proved from the machine-checked balance only; no estimate is
involved.  Combined with the dichotomy of `LiteralWeilClusterTwoRadiusProfile` it
converts an off-line zero at the ordinate `t` into a **strict orientation
requirement** on the residual channels read at the two radii:

    some zero of the fibre off the line  ⟹  R(2r) A_0(r) - R(r) A_0(2r) > 0.

That is the sharpened form of the first genuine estimate: not "the residual
channels are small", but "the residual channels must point in one specific
projective direction".  Nothing here asserts that they do or do not.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile

noncomputable section

open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilTwoRadiusBalance

open Zeta23Bridge.LiteralWeilParityBalance Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilEvenChannelTaper Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile

/-- The total residual cone value at sampling radius `s`: everything in the literal
balance other than the same-ordinate cluster. -/
def residualCone (g : ℝ → ℝ) (t s : ℝ) : ℝ :=
  evenConeFunctional (offOrdVec (sampleFam g t s) t)
    + evenConeFunctional (primeVec (sampleFam g t s))
    + evenConeFunctional (gammaVec (sampleFam g t s))
    + evenConeFunctional (poleVec (sampleFam g t s))

/-- **The balance, read by the even cone functional at one radius.** -/
theorem clusterCone_eq_neg_residual {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (t s : ℝ) :
    evenConeFunctional (clusterVec (sampleFam g t s) t) = -residualCone g t s := by
  have hbal := literalWeilOrdinateFibreBalance (fun i => sampleFam_contDiff hgs t s i)
    (fun i => sampleFam_hasCompactSupport hgc t s i) t
  have hlin : evenConeFunctional (clusterVec (sampleFam g t s) t)
      + evenConeFunctional (offOrdVec (sampleFam g t s) t)
      + evenConeFunctional (primeVec (sampleFam g t s))
      + evenConeFunctional (gammaVec (sampleFam g t s))
      + evenConeFunctional (poleVec (sampleFam g t s)) = 0 := by
    rw [← map_add, ← map_add, ← map_add, ← map_add, hbal, map_zero]
  unfold residualCone
  linarith

/-- The cluster's two-radius profile, expressed through the residual channels. -/
theorem clusterTwoRadiusProfile_eq {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    clusterTwoRadiusProfile g t r = (-residualCone g t r, -residualCone g t (2 * r)) := by
  have h1 := clusterVec_cone_value hgs hgc heven t r
  have h2 := clusterVec_cone_value hgs hgc heven t (2 * r)
  have e1 := clusterCone_eq_neg_residual hgs hgc t r
  have e2 := clusterCone_eq_neg_residual hgs hgc t (2 * r)
  unfold clusterTwoRadiusProfile
  rw [← h1, ← h2, e1, e2]

/-- **`twoRadiusResidualBalance`.**  The exact two-radius form of the literal Weil
balance: the cluster height defect is minus the corresponding determinant of the
residual channels against the on-line profile. -/
theorem twoRadiusResidualBalance {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    clusterHeightDefect g t r
      = -(residualCone g t r * evenResp g 0 (2 * r)
          - residualCone g t (2 * r) * evenResp g 0 r) := by
  unfold clusterHeightDefect profileDefect evenProfile
  rw [clusterTwoRadiusProfile_eq hgs hgc heven t r]
  ring

/-- **`offLineZeroForcesResidualOrientation`.**  An off-line zero in the fibre at a
nonzero ordinate forces a strict projective orientation on the residual channels
read at the two radii.  For the explicit positive taper that kills the pole channel
at the base radius:

    heightOf ρ₀ ≠ 0  ⟹  R(2r) A_0(r) - R(r) A_0(2r) > 0,

and, when the whole fibre is on the critical line, the same quantity is exactly
zero.  This is the sharpened target of the first genuine estimate: a required
*direction*, not merely a required smallness. -/
theorem offLineZeroForcesResidualOrientation {t : ℝ} (ht : t ≠ 0) :
    ∃ (g : ℝ → ℝ) (r : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r ∧ poleEvenResp g t r = 0
      ∧ (∀ ρ₀ : SameOrd t, heightOf (ρ₀ : Zeros) ≠ 0 →
          0 < residualCone g t (2 * r) * evenResp g 0 r
              - residualCone g t r * evenResp g 0 (2 * r))
      ∧ ((∀ ρ : SameOrd t, heightOf (ρ : Zeros) = 0) →
          residualCone g t (2 * r) * evenResp g 0 r
            - residualCone g t r * evenResp g 0 (2 * r) = 0) := by
  obtain ⟨g, r, hgs, hgc, heven, hr, hnn, hrad, ⟨u₀, v₀, hu₀, hv₀, hne⟩, hpole, -, -⟩ :=
    exists_positive_taper_poleEven_zero ht
  have hbal := twoRadiusResidualBalance hgs hgc heven t r
  refine ⟨g, r, hgs, hgc, heven, hr, hpole, ?_, ?_⟩
  · intro ρ₀ hρ₀
    have hpos : 0 < clusterHeightDefect g t r :=
      literalClusterTwoRadiusDetectsOffLine hgs hgc heven hnn hr hrad hu₀ hv₀ hne ρ₀ hρ₀
    linarith [hbal ▸ hpos]
  · intro hall
    have hzero : clusterHeightDefect g t r = 0 :=
      clusterHeightDefect_eq_zero_of_onLine hgs hgc heven t r hall
    linarith [hbal ▸ hzero]

end LiteralWeilTwoRadiusBalance
end Zeta23Bridge
