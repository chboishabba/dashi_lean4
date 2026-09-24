/-
# Projectivizing the residual: the exact channel-by-channel determinant decomposition

`LiteralWeilTwoRadiusBalance.twoRadiusResidualBalance` is the exact identity

    D_cluster(t, r) = R(2r) A_0(r) - R(r) A_0(2r),
    R(s) = ℓ(Q_offOrd) + ℓ(Q_prime) + ℓ(Q_Γ) + ℓ(Q_pole)   at sampling radius s.

`LiteralWeilTwoRadiusResidualEnvelope` bounded the right-hand side by taking
absolute values *radius by radius*,

    |R(2r) A_0(r) - R(r) A_0(2r)| ≤ |R(2r)| |A_0(r)| + |R(r)| |A_0(2r)|,

which throws away all cancellation between the two radii.  This module takes the
first step of the projective tranche: it *projectivizes each channel before any
majorization*.

For a scalar channel `C : ℝ → ℝ` (a function of the sampling radius) put

    𝔇_C(r) = C(2r) A_0(r) - C(r) A_0(2r)      (`channelProjectiveDefect`).

`𝔇` is additive in the channel (it is a determinant with a fixed second column),
so the exact decomposition

    𝔇_R = 𝔇_{Z_off} + 𝔇_prime + 𝔇_Γ + 𝔇_Π                (`residualProjectiveDecomposition`)

holds by linearity alone, and the literal balance turns it into

    D_cluster(t, r) = 𝔇_{Z_off} + 𝔇_prime + 𝔇_Γ + 𝔇_Π .

Under the short taper the prime channel vanishes at *every* sampling radius
(`LiteralWeilPrimeEvenCone.primeConeValue_eq_zero_of_short_taper`), hence

    𝔇_prime = 0                                        (`primeProjectiveDefect_eq_zero`)

exactly, and the literal cluster defect is carried by three channels only:

    D_cluster(t, r) = 𝔇_{Z_off} + 𝔇_Γ + 𝔇_Π            (`clusterHeightDefect_eq_threeProjectiveChannels`).

Nothing here is an estimate; every statement is an identity proved by linearity.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilTwoRadiusResidualEnvelope

noncomputable section

open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilProjectiveResidualDecomposition

open Zeta23Bridge.LiteralWeilParityBalance Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilEvenChannelTaper Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilTwoRadiusBalance
open Zeta23Bridge.LiteralWeilOffOrdinateTail Zeta23Bridge.LiteralWeilGammaConeBound
open Zeta23Bridge.LiteralWeilPrimeEvenCone
open Zeta23Bridge.LiteralWeilTwoRadiusResidualEnvelope

/-! ## The projective defect of a scalar channel -/

/-- **The projective (two-radius determinant) defect of a channel.**  For a scalar
channel `C`, read as a function of the sampling radius, this is the determinant of
`(C(r), C(2r))` against the on-line profile `(A_0(r), A_0(2r))`:

    𝔇_C(r) = C(2r) A_0(r) - C(r) A_0(2r).

This is the observable the literal two-radius balance actually constrains; it is
*not* obtained by estimating `C(r)` and `C(2r)` separately. -/
def channelProjectiveDefect (C : ℝ → ℝ) (g : ℝ → ℝ) (r : ℝ) : ℝ :=
  C (2 * r) * evenResp g 0 r - C r * evenResp g 0 (2 * r)

/-- The projective defect is additive in the channel. -/
theorem channelProjectiveDefect_add (C D : ℝ → ℝ) (g : ℝ → ℝ) (r : ℝ) :
    channelProjectiveDefect (fun s => C s + D s) g r
      = channelProjectiveDefect C g r + channelProjectiveDefect D g r := by
  unfold channelProjectiveDefect; ring

/-- The projective defect is homogeneous in the channel. -/
theorem channelProjectiveDefect_smul (c : ℝ) (C : ℝ → ℝ) (g : ℝ → ℝ) (r : ℝ) :
    channelProjectiveDefect (fun s => c * C s) g r = c * channelProjectiveDefect C g r := by
  unfold channelProjectiveDefect; ring

/-- A channel vanishing at both sampling radii has zero projective defect. -/
theorem channelProjectiveDefect_eq_zero {C : ℝ → ℝ} {g : ℝ → ℝ} {r : ℝ}
    (h1 : C r = 0) (h2 : C (2 * r) = 0) : channelProjectiveDefect C g r = 0 := by
  unfold channelProjectiveDefect; rw [h1, h2]; ring

/-! ## The four literal channels, as functions of the sampling radius -/

/-- The off-ordinate zero channel at sampling radius `s`. -/
def offOrdChannel (g : ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  fun s => evenConeFunctional (offOrdVec (sampleFam g t s) t)

/-- The prime channel at sampling radius `s`. -/
def primeChannel (g : ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  fun s => evenConeFunctional (primeVec (sampleFam g t s))

/-- The gamma channel at sampling radius `s`. -/
def gammaChannel (g : ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  fun s => evenConeFunctional (gammaVec (sampleFam g t s))

/-- The pole channel at sampling radius `s`. -/
def poleChannel (g : ℝ → ℝ) (t : ℝ) : ℝ → ℝ :=
  fun s => evenConeFunctional (poleVec (sampleFam g t s))

theorem residualCone_eq_channels (g : ℝ → ℝ) (t s : ℝ) :
    residualCone g t s
      = offOrdChannel g t s + primeChannel g t s + gammaChannel g t s + poleChannel g t s :=
  rfl

/-! ## The four projective defects -/

/-- `𝔇_R`: the projective defect of the total residual. -/
def residualProjectiveDefect (g : ℝ → ℝ) (t r : ℝ) : ℝ :=
  channelProjectiveDefect (residualCone g t) g r

/-- `𝔇_{Z_off}`: the projective defect of the off-ordinate zero channel. -/
def offOrdProjectiveDefect (g : ℝ → ℝ) (t r : ℝ) : ℝ :=
  channelProjectiveDefect (offOrdChannel g t) g r

/-- `𝔇_prime`: the projective defect of the prime channel. -/
def primeProjectiveDefect (g : ℝ → ℝ) (t r : ℝ) : ℝ :=
  channelProjectiveDefect (primeChannel g t) g r

/-- `𝔇_Γ`: the projective defect of the gamma channel. -/
def gammaProjectiveDefect (g : ℝ → ℝ) (t r : ℝ) : ℝ :=
  channelProjectiveDefect (gammaChannel g t) g r

/-- `𝔇_Π`: the projective defect of the pole channel. -/
def poleProjectiveDefect (g : ℝ → ℝ) (t r : ℝ) : ℝ :=
  channelProjectiveDefect (poleChannel g t) g r

/-- **`residualProjectiveDecomposition`.**  The exact channel-by-channel projective
decomposition, by linearity of the determinant in its first column. -/
theorem residualProjectiveDecomposition (g : ℝ → ℝ) (t r : ℝ) :
    residualProjectiveDefect g t r
      = offOrdProjectiveDefect g t r + primeProjectiveDefect g t r
        + gammaProjectiveDefect g t r + poleProjectiveDefect g t r := by
  unfold residualProjectiveDefect offOrdProjectiveDefect primeProjectiveDefect
    gammaProjectiveDefect poleProjectiveDefect channelProjectiveDefect
  simp only [residualCone_eq_channels]
  ring

/-! ## The prime channel is projectively absent in the short-taper lane -/

/-- **`primeProjectiveDefect_eq_zero`.**  A taper supported in `|u| < log 2` misses
every literal prime frequency, at *every* sampling radius; hence its prime
projective defect vanishes identically. -/
theorem primeProjectiveDefect_eq_zero {g : ℝ → ℝ}
    (hshort : ∀ u, g u ≠ 0 → |u| < Real.log 2) (t r : ℝ) :
    primeProjectiveDefect g t r = 0 :=
  channelProjectiveDefect_eq_zero (primeConeValue_eq_zero_of_short_taper hshort t r)
    (primeConeValue_eq_zero_of_short_taper hshort t (2 * r))

/-! ## The pole channel's projective defect, in closed form -/

/-- **`poleProjectiveDefect_eq`.**  The even cone reads the pole channel as the
exact number `-4 P_t(s)`, so its projective defect is `-4` times the determinant of
the pole profile against the on-line profile. -/
theorem poleProjectiveDefect_eq {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    poleProjectiveDefect g t r
      = -4 * (poleEvenResp g t (2 * r) * evenResp g 0 r
              - poleEvenResp g t r * evenResp g 0 (2 * r)) := by
  unfold poleProjectiveDefect channelProjectiveDefect poleChannel
  rw [poleCone_value hg hgc heven t (2 * r), poleCone_value hg hgc heven t r]
  ring

/-! ## The literal balance in projective form -/

/-- **`clusterHeightDefect_eq_residualProjectiveDefect`.**  The literal two-radius
balance says exactly that the cluster height defect *is* the residual's projective
defect. -/
theorem clusterHeightDefect_eq_residualProjectiveDefect {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    clusterHeightDefect g t r = residualProjectiveDefect g t r := by
  rw [twoRadiusResidualBalance hgs hgc heven t r]
  unfold residualProjectiveDefect channelProjectiveDefect
  ring

/-- **`clusterHeightDefect_eq_fourProjectiveChannels`.**  The literal balance,
projectivized channel by channel. -/
theorem clusterHeightDefect_eq_fourProjectiveChannels {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    clusterHeightDefect g t r
      = offOrdProjectiveDefect g t r + primeProjectiveDefect g t r
        + gammaProjectiveDefect g t r + poleProjectiveDefect g t r := by
  rw [clusterHeightDefect_eq_residualProjectiveDefect hgs hgc heven t r,
    residualProjectiveDecomposition]

/-- **`clusterHeightDefect_eq_threeProjectiveChannels`.**  In the short-taper lane
the prime channel is projectively absent and the literal cluster height defect is
carried by exactly three projective channels. -/
theorem clusterHeightDefect_eq_threeProjectiveChannels {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u)
    (hshort : ∀ u, g u ≠ 0 → |u| < Real.log 2) (t r : ℝ) :
    clusterHeightDefect g t r
      = offOrdProjectiveDefect g t r + gammaProjectiveDefect g t r
        + poleProjectiveDefect g t r := by
  rw [clusterHeightDefect_eq_fourProjectiveChannels hgs hgc heven t r,
    primeProjectiveDefect_eq_zero hshort t r]
  ring

end LiteralWeilProjectiveResidualDecomposition
end Zeta23Bridge
