/-
# The literal same-ordinate cluster carries its heights in the two-radius profile

`LiteralWeilSameOrdinateEvenCone` proved that the same-ordinate cluster has a
strictly positive even cone value, so that reflection pairs at the target ordinate
cannot cancel one another.  `LiteralWeilTwoRadiusHeightDetector` proved that parity
alone cannot distinguish an off-line height from an on-line one, but that the
*two-radius* projective shape can, both for a single height and for a finite
positively weighted cluster of heights.

This module combines the two at the *literal* level: the cluster of **all**
nontrivial zeros with imaginary part `t`, with their genuine multiplicities.  Its
two-radius profile is

    P(t, r) = ( Σ_ρ 2 m_ρ A_{a_ρ}(r) , Σ_ρ 2 m_ρ A_{a_ρ}(2r) ),   a_ρ = Re ρ - 1/2,

both sums over the fibre `SameOrd t`, both absolutely convergent.  The literal
cluster height defect is the determinant of `P(t, r)` against the on-line profile
`(A_0(r), A_0(2r))`.

The two results are a sharp dichotomy for the fibre, for a nonnegative radially
admissible taper:

* `literalClusterTwoRadiusDetectsOffLine` — if a single zero of the fibre is off
  the critical line, the cluster defect is **strictly positive**;
* `clusterHeightDefect_eq_zero_of_onLine` — if every zero of the fibre is on the
  critical line, the cluster defect is **exactly zero**.

`literalTwoRadiusClusterDichotomy` states both for the explicit taper that kills
the pole channel.

This is a discriminator, not yet a contradiction: turning the positivity into a
refutation of an off-line zero still requires controlling the off-ordinate, prime
and gamma channels in the same two-radius geometry.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

noncomputable section

open MeasureTheory
open scoped Real

namespace Zeta23Bridge
namespace LiteralWeilClusterTwoRadiusProfile

open Zeta23Bridge.LiteralWeilParityBalance Zeta23Bridge.LiteralWeilOtherZerosChannel
open Zeta23Bridge.LiteralWeilEvenChannelTaper Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

/-- The literal two-radius profile of the whole same-ordinate cluster: the pair of
cone weights at the base radius `r` and at the doubled radius `2r`. -/
def clusterTwoRadiusProfile (g : ℝ → ℝ) (t r : ℝ) : ℝ × ℝ :=
  (∑' ρ : SameOrd t, coneWeight g r (ρ : Zeros),
    ∑' ρ : SameOrd t, coneWeight g (2 * r) (ρ : Zeros))

/-- The literal cluster height defect: the determinant of the cluster's two-radius
profile against the on-line profile. -/
def clusterHeightDefect (g : ℝ → ℝ) (t r : ℝ) : ℝ :=
  profileDefect (clusterTwoRadiusProfile g t r) (evenProfile g r 0)

/-- The per-zero contribution to the cluster defect. -/
def zeroHeightDefect (g : ℝ → ℝ) (r : ℝ) (ρ : Zeros) : ℝ :=
  2 * ((Zeta23.zetaZeroConfig).mult ρ : ℝ) * heightDefect g r (heightOf ρ) 0

theorem coneWeight_mul_sub {g : ℝ → ℝ} (r : ℝ) (ρ : Zeros) :
    coneWeight g r ρ * evenResp g 0 (2 * r) - coneWeight g (2 * r) ρ * evenResp g 0 r
      = zeroHeightDefect g r ρ := by
  unfold coneWeight zeroHeightDefect heightDefect
  ring

theorem summable_zeroHeightDefect {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    Summable fun ρ : SameOrd t => zeroHeightDefect g r (ρ : Zeros) := by
  have h1 := (summable_coneWeight hgs hgc heven t r).mul_right (evenResp g 0 (2 * r))
  have h2 := (summable_coneWeight hgs hgc heven t (2 * r)).mul_right (evenResp g 0 r)
  refine (h1.sub h2).congr (fun ρ => ?_)
  exact coneWeight_mul_sub r (ρ : Zeros)

/-- **The cluster defect is the sum of the per-zero defects.**  The determinant is
bilinear, so the (absolutely convergent) cluster sums pass through it. -/
theorem clusterHeightDefect_eq_tsum {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (t r : ℝ) :
    clusterHeightDefect g t r = ∑' ρ : SameOrd t, zeroHeightDefect g r (ρ : Zeros) := by
  have h1 := (summable_coneWeight hgs hgc heven t r).mul_right (evenResp g 0 (2 * r))
  have h2 := (summable_coneWeight hgs hgc heven t (2 * r)).mul_right (evenResp g 0 r)
  have hsub : (∑' ρ : SameOrd t, coneWeight g r (ρ : Zeros) * evenResp g 0 (2 * r))
      - (∑' ρ : SameOrd t, coneWeight g (2 * r) (ρ : Zeros) * evenResp g 0 r)
      = ∑' ρ : SameOrd t, zeroHeightDefect g r (ρ : Zeros) := by
    rw [← h1.tsum_sub h2]
    exact tsum_congr fun ρ => coneWeight_mul_sub r (ρ : Zeros)
  unfold clusterHeightDefect profileDefect clusterTwoRadiusProfile evenProfile
  simpa [tsum_mul_right] using hsub

theorem zeroHeightDefect_nonneg {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hnn : ∀ u, 0 ≤ g u) {r : ℝ} (hr : 0 < r)
    (hrad : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2) (ρ : Zeros) :
    0 ≤ zeroHeightDefect g r ρ := by
  have hm : (0 : ℝ) ≤ ((Zeta23.zetaZeroConfig).mult ρ : ℝ) := by positivity
  have hD : 0 ≤ heightDefect g r (heightOf ρ) 0 :=
    heightDefect_nonneg hg hgc hnn hr hrad (by simp)
  unfold zeroHeightDefect
  positivity

theorem zeroHeightDefect_pos {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hnn : ∀ u, 0 ≤ g u) {r : ℝ} (hr : 0 < r)
    (hrad : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2)
    {u₀ v₀ : ℝ} (hu₀ : 0 < g u₀) (hv₀ : 0 < g v₀) (hne : |u₀| ≠ |v₀|)
    {ρ : Zeros} (hρ : heightOf ρ ≠ 0) : 0 < zeroHeightDefect g r ρ := by
  have hm : (1 : ℕ) ≤ (Zeta23.zetaZeroConfig).mult ρ :=
    (Zeta23.zetaZeroConfig).one_le_mult (ρ : ℂ) ρ.2
  have hmR : (0 : ℝ) < ((Zeta23.zetaZeroConfig).mult ρ : ℝ) := by exact_mod_cast hm
  have hD : 0 < heightDefect g r (heightOf ρ) 0 :=
    twoRadiusEvenProfileDetectsHeight hg hgc hnn hr hrad hu₀ hv₀ hne hρ
  unfold zeroHeightDefect
  positivity

/-- **`literalClusterTwoRadiusDetectsOffLine`.**  A single off-line zero in the
fibre forces the whole literal same-ordinate cluster off the on-line projective
direction: the cluster height defect is strictly positive.  No cancellation among
the other zeros of the fibre — of any heights, with any multiplicities — can undo
it, because every per-zero defect is nonnegative. -/
theorem literalClusterTwoRadiusDetectsOffLine {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (hnn : ∀ u, 0 ≤ g u)
    {t r : ℝ} (hr : 0 < r) (hrad : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2)
    {u₀ v₀ : ℝ} (hu₀ : 0 < g u₀) (hv₀ : 0 < g v₀) (hne : |u₀| ≠ |v₀|)
    (ρ₀ : SameOrd t) (hρ₀ : heightOf (ρ₀ : Zeros) ≠ 0) :
    0 < clusterHeightDefect g t r := by
  rw [clusterHeightDefect_eq_tsum hgs hgc heven t r]
  exact Summable.tsum_pos (summable_zeroHeightDefect hgs hgc heven t r)
    (fun ρ => zeroHeightDefect_nonneg hgs.continuous hgc hnn hr hrad (ρ : Zeros)) ρ₀
    (zeroHeightDefect_pos hgs.continuous hgc hnn hr hrad hu₀ hv₀ hne hρ₀)

/-- The exact converse: an entirely on-line fibre has vanishing cluster defect, so
the two-radius profile is a *sharp* discriminator. -/
theorem clusterHeightDefect_eq_zero_of_onLine {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (t r : ℝ)
    (hall : ∀ ρ : SameOrd t, heightOf (ρ : Zeros) = 0) :
    clusterHeightDefect g t r = 0 := by
  rw [clusterHeightDefect_eq_tsum hgs hgc heven t r]
  have hzero : (fun ρ : SameOrd t => zeroHeightDefect g r (ρ : Zeros)) = fun _ => 0 := by
    funext ρ
    unfold zeroHeightDefect
    rw [hall ρ, heightDefect_self]
    ring
  rw [hzero, tsum_zero]

/-- **`literalTwoRadiusClusterDichotomy`.**  For every nonzero target ordinate the
explicit positive taper that annihilates the pole channel also turns the literal
same-ordinate cluster into a sharp on-line/off-line discriminator: the cluster
height defect is strictly positive as soon as one zero of the fibre is off the
critical line, and exactly zero when the whole fibre is on it.

This is a discriminator, not a contradiction: refuting an off-line zero from it
still requires controlling the off-ordinate, prime and gamma channels in the same
two-radius geometry. -/
theorem literalTwoRadiusClusterDichotomy {t : ℝ} (ht : t ≠ 0) :
    ∃ (g : ℝ → ℝ) (r : ℝ), ContDiff ℝ 2 g ∧ HasCompactSupport g ∧ (∀ u, g (-u) = g u)
      ∧ 0 < r ∧ poleEvenResp g t r = 0
      ∧ (∀ ρ₀ : SameOrd t, heightOf (ρ₀ : Zeros) ≠ 0 → 0 < clusterHeightDefect g t r)
      ∧ ((∀ ρ : SameOrd t, heightOf (ρ : Zeros) = 0) → clusterHeightDefect g t r = 0) := by
  obtain ⟨g, r, hgs, hgc, heven, hr, hnn, hrad, ⟨u₀, v₀, hu₀, hv₀, hne⟩, hpole, -, -⟩ :=
    exists_positive_taper_poleEven_zero ht
  refine ⟨g, r, hgs, hgc, heven, hr, hpole, ?_, ?_⟩
  · intro ρ₀ hρ₀
    exact literalClusterTwoRadiusDetectsOffLine hgs hgc heven hnn hr hrad hu₀ hv₀ hne ρ₀ hρ₀
  · intro hall
    exact clusterHeightDefect_eq_zero_of_onLine hgs hgc heven t r hall

/-- **The cluster defect dominates the defect of any single zero of the fibre.**
Every per-zero contribution is nonnegative, so a lower bound for the cluster defect
is available from the target zero alone:

    D_cluster(t, r) ≥ 2 m_{ρ₀} D(a_{ρ₀}, 0).

This is the shape any future quantitative separation would use on the signal
side. -/
theorem clusterHeightDefect_ge_zeroHeightDefect {g : ℝ → ℝ} (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (heven : ∀ u, g (-u) = g u) (hnn : ∀ u, 0 ≤ g u)
    {t r : ℝ} (hr : 0 < r) (hrad : ∀ u, g u ≠ 0 → 2 * r * |u| < π / 2) (ρ₀ : SameOrd t) :
    zeroHeightDefect g r (ρ₀ : Zeros) ≤ clusterHeightDefect g t r := by
  classical
  rw [clusterHeightDefect_eq_tsum hgs hgc heven t r]
  have := Summable.sum_le_tsum (f := fun ρ : SameOrd t => zeroHeightDefect g r (ρ : Zeros))
    {ρ₀} (fun i _ => zeroHeightDefect_nonneg hgs.continuous hgc hnn hr hrad (i : Zeros))
    (summable_zeroHeightDefect hgs hgc heven t r)
  simpa using this

end LiteralWeilClusterTwoRadiusProfile
end Zeta23Bridge
