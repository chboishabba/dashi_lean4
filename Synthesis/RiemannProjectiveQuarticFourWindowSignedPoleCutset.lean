import Synthesis.RiemannProjectiveQuarticFourWindowSignedPolePair
import Synthesis.RiemannProjectiveQuarticFourWindowHighCutset
import Synthesis.RiemannCanonicalTargetPairResidual

/-!
# Signed two-detector high cutset after exact pole cancellation

A signed pole-cancelled endpoint pair no longer has nonnegative coefficients,
but its *combined source observable* has a positive punctured height band.

When 8/t lies inside that band, every same-ordinate zero contributes
nonnegatively to the combined cluster and every off-line one contributes
strictly positively.  Reflection gives the target partner the same combined
defect, so

  2 D_comb(rho) <= C_comb.

Linearity of the two literal projective explicit formulas gives

  C_comb
    = P2 (Doff_1 + DGamma_1 + Dpole_1)
      - P1 (Doff_2 + DGamma_2 + Dpole_2).

The pole terms cancel exactly by construction, leaving

  C_comb
    = P2 (Doff_1 + DGamma_1)
      - P1 (Doff_2 + DGamma_2).

Thus the four-window signed route has genuinely removed the positive pole
obstruction while retaining target-pair positivity.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair

def QuarticFourSignedPolePair.combinedCluster
    {t : ℝ} (W : QuarticFourSignedPolePair t) : ℝ :=
  W.poleTwo *
      clusterHeightDefect
        (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
        t (t/16)
    +
  (-W.poleHalf) *
      clusterHeightDefect
        (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
        t (t/16)

theorem QuarticFourSignedPolePair.combinedZeroHeightDefect_eq_linear
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.combinedZeroHeightDefect rho
      =
    W.poleTwo *
      zeroHeightDefect
        (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
        (t/16) rho
      +
    (-W.poleHalf) *
      zeroHeightDefect
        (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
        (t/16) rho := by
  unfold QuarticFourSignedPolePair.combinedZeroHeightDefect
    QuarticFourSignedPolePair.physicalCombinedHeightDefect
    zeroHeightDefect
  ring

theorem QuarticFourSignedPolePair.combinedSource_summable
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    Summable fun z : SameOrd t =>
      W.combinedZeroHeightDefect (z : Zeros) := by
  have h1 :
      Summable fun z : SameOrd t =>
        zeroHeightDefect
          (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
          (t/16) (z : Zeros) :=
    summable_zeroHeightDefect
      (quarticFourPhysicalDetector_contDiff
        (t:=t) (lam:=(1/2 : ℝ)) (mu:=W.muHalf) W.Rpos)
      (quarticFourPhysicalDetector_compact
        (t:=t) (lam:=(1/2 : ℝ)) (mu:=W.muHalf) W.Rpos ht)
      (quarticFourPhysicalDetector_even W.R (1/2) W.muHalf t)
      t (t/16)
  have h2 :
      Summable fun z : SameOrd t =>
        zeroHeightDefect
          (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
          (t/16) (z : Zeros) :=
    summable_zeroHeightDefect
      (quarticFourPhysicalDetector_contDiff
        (t:=t) (lam:=(2/3 : ℝ)) (mu:=W.muTwo) W.Rpos)
      (quarticFourPhysicalDetector_compact
        (t:=t) (lam:=(2/3 : ℝ)) (mu:=W.muTwo) W.Rpos ht)
      (quarticFourPhysicalDetector_even W.R (2/3) W.muTwo t)
      t (t/16)
  have hs :=
    (h1.mul_left W.poleTwo).add
      (h2.mul_left (-W.poleHalf))
  refine hs.congr ?_
  intro z
  rw [W.combinedZeroHeightDefect_eq_linear]

theorem QuarticFourSignedPolePair.combinedCluster_eq_tsum
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t) :
    W.combinedCluster
      =
    ∑' z : SameOrd t,
      W.combinedZeroHeightDefect (z : Zeros) := by
  have h1 :=
    clusterHeightDefect_eq_tsum
      (quarticFourPhysicalDetector_contDiff
        (t:=t) (lam:=(1/2 : ℝ)) (mu:=W.muHalf) W.Rpos)
      (quarticFourPhysicalDetector_compact
        (t:=t) (lam:=(1/2 : ℝ)) (mu:=W.muHalf) W.Rpos ht)
      (quarticFourPhysicalDetector_even W.R (1/2) W.muHalf t)
      t (t/16)
  have h2 :=
    clusterHeightDefect_eq_tsum
      (quarticFourPhysicalDetector_contDiff
        (t:=t) (lam:=(2/3 : ℝ)) (mu:=W.muTwo) W.Rpos)
      (quarticFourPhysicalDetector_compact
        (t:=t) (lam:=(2/3 : ℝ)) (mu:=W.muTwo) W.Rpos ht)
      (quarticFourPhysicalDetector_even W.R (2/3) W.muTwo t)
      t (t/16)
  have hs1 :
      Summable fun z : SameOrd t =>
        zeroHeightDefect
          (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
          (t/16) (z : Zeros) :=
    summable_zeroHeightDefect
      (quarticFourPhysicalDetector_contDiff
        (t:=t) (lam:=(1/2 : ℝ)) (mu:=W.muHalf) W.Rpos)
      (quarticFourPhysicalDetector_compact
        (t:=t) (lam:=(1/2 : ℝ)) (mu:=W.muHalf) W.Rpos ht)
      (quarticFourPhysicalDetector_even W.R (1/2) W.muHalf t)
      t (t/16)
  have hs2 :
      Summable fun z : SameOrd t =>
        zeroHeightDefect
          (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
          (t/16) (z : Zeros) :=
    summable_zeroHeightDefect
      (quarticFourPhysicalDetector_contDiff
        (t:=t) (lam:=(2/3 : ℝ)) (mu:=W.muTwo) W.Rpos)
      (quarticFourPhysicalDetector_compact
        (t:=t) (lam:=(2/3 : ℝ)) (mu:=W.muTwo) W.Rpos ht)
      (quarticFourPhysicalDetector_even W.R (2/3) W.muTwo t)
      t (t/16)
  unfold QuarticFourSignedPolePair.combinedCluster
  rw [h1,h2, ← tsum_mul_left, ← tsum_mul_left]
  rw [← (hs1.mul_left W.poleTwo).tsum_add
      (hs2.mul_left (-W.poleHalf))]
  apply tsum_congr
  intro z
  rw [W.combinedZeroHeightDefect_eq_linear]

theorem QuarticFourSignedPolePair.combined_reflect_eq
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    (rho : Zeros) :
    W.combinedZeroHeightDefect (reflectZero rho)
      = W.combinedZeroHeightDefect rho := by
  rw [W.combinedZeroHeightDefect_eq_linear,
      W.combinedZeroHeightDefect_eq_linear]
  unfold zeroHeightDefect
  rw [reflectZero_mult,heightOf_reflectZero,
      heightDefect_neg_height,heightDefect_neg_height]

theorem QuarticFourSignedPolePair.targetPair_sum_eq_two
    {t : ℝ} (W : QuarticFourSignedPolePair t)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    (∑ z ∈ canonicalTargetPairFinset rho him,
      W.combinedZeroHeightDefect (z : Zeros))
      =
    2 * W.combinedZeroHeightDefect rho := by
  let z0 : SameOrd t := ⟨rho,him⟩
  let z1 : SameOrd t :=
    ⟨reflectZero rho, by
      rw [im_reflectZero]
      exact him⟩
  have hne : z1 ≠ z0 := by
    intro h
    have hv : (z1 : Zeros) = (z0 : Zeros) :=
      congrArg Subtype.val h
    dsimp [z0,z1] at hv
    exact (reflectZero_ne_of_height_ne_zero hoff) hv
  unfold canonicalTargetPairFinset
  change
    (∑ z ∈ ({z0,z1} : Finset (SameOrd t)),
      W.combinedZeroHeightDefect (z : Zeros)) = _
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    dsimp [z0,z1]
    rw [W.combined_reflect_eq]
    ring
  · simpa [Finset.mem_singleton] using hne

theorem QuarticFourSignedPolePair.two_target_le_combinedCluster
    {t : ℝ} (ht : 0 < t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.eps)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    2 * W.combinedZeroHeightDefect rho
      <= W.combinedCluster := by
  have hs := W.combinedSource_summable ht
  have hsplit :=
    hs.sum_add_tsum_compl
      (s:=canonicalTargetPairFinset rho him)
  rw [W.combinedCluster_eq_tsum ht]
  rw [← hsplit, W.targetPair_sum_eq_two him hoff]
  exact le_add_of_nonneg_right
    (tsum_nonneg fun z =>
      W.combinedZeroHeightDefect_nonneg ht hhigh
        ((z : SameOrd t) : Zeros))

theorem QuarticFourSignedPolePair.combinedCluster_eq_offGamma
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t) :
    W.combinedCluster
      =
    W.poleTwo *
      (offOrdProjectiveDefect
          (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
          t (t/16)
        +
       gammaProjectiveDefect
          (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
          t (t/16))
      +
    (-W.poleHalf) *
      (offOrdProjectiveDefect
          (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
          t (t/16)
        +
       gammaProjectiveDefect
          (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
          t (t/16)) := by
  -- Avoid manufacturing target-band data: use the literal cluster identity
  -- directly for the two physical profiles.
  have htpos : 0 < t := by linarith
  have hc1 :=
    clusterHeightDefect_eq_threeProjectiveChannels
      (quarticFourPhysicalDetector_contDiff
        (t:=t) (lam:=(1/2 : ℝ)) (mu:=W.muHalf) W.Rpos)
      (quarticFourPhysicalDetector_compact
        (t:=t) (lam:=(1/2 : ℝ)) (mu:=W.muHalf) W.Rpos htpos)
      (quarticFourPhysicalDetector_even W.R (1/2) W.muHalf t)
      (quarticFourPhysicalDetector_short_of_twoHundred
        W.Rpos W.RltOne ht)
      t (t/16)
  have hc2 :=
    clusterHeightDefect_eq_threeProjectiveChannels
      (quarticFourPhysicalDetector_contDiff
        (t:=t) (lam:=(2/3 : ℝ)) (mu:=W.muTwo) W.Rpos)
      (quarticFourPhysicalDetector_compact
        (t:=t) (lam:=(2/3 : ℝ)) (mu:=W.muTwo) W.Rpos htpos)
      (quarticFourPhysicalDetector_even W.R (2/3) W.muTwo t)
      (quarticFourPhysicalDetector_short_of_twoHundred
        W.Rpos W.RltOne ht)
      t (t/16)
  unfold QuarticFourSignedPolePair.combinedCluster
  rw [hc1,hc2]
  have hpole := W.literalPole_cancel htpos
  linarith

/--
Prize-facing signed pole-cancelled cutset.
-/
theorem false_of_quarticFourSignedPole_external_strict
    {t : ℝ} (ht : 200 <= t)
    (W : QuarticFourSignedPolePair t)
    (hhigh : 8/t < W.eps)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0)
    (hstrict :
      W.poleTwo *
        (offOrdProjectiveDefect
            (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
            t (t/16)
          +
         gammaProjectiveDefect
            (quarticFourPhysicalDetector W.R (1/2) W.muHalf t)
            t (t/16))
        +
      (-W.poleHalf) *
        (offOrdProjectiveDefect
            (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
            t (t/16)
          +
         gammaProjectiveDefect
            (quarticFourPhysicalDetector W.R (2/3) W.muTwo t)
            t (t/16))
      <
      2 * W.combinedZeroHeightDefect rho) :
    False := by
  have hlo :=
    W.two_target_le_combinedCluster
      (by linarith : 0 < t) hhigh him hoff
  rw [W.combinedCluster_eq_offGamma ht] at hlo
  linarith

end Synthesis
