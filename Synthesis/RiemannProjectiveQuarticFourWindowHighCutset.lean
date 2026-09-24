import Synthesis.RiemannProjectiveQuarticFourWindowHighWitness
import Synthesis.RiemannCanonicalTargetPairResidual
import Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
import Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
import Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair

/-!
# Prize-facing high cutset for the four-window quartic family

The four-window witness has the same target-pair geometry as the established
three-window quartic detector, but retains lambda as a free design parameter.

At sufficiently high ordinate:
* every same-ordinate defect is nonnegative;
* the reflected partner of an off-line target has the same positive defect;
* the physical support is below log 2, so the prime channel vanishes exactly.

Hence

  2 D_rho <= D_cluster
            = D_off^proj + D_Gamma^proj + D_pole^proj.

Any independent strict upper on the three external channels below 2 D_rho is
therefore contradictory.  This is the consumer needed for optimizing the free
four-window parameter against the external scalar channels.
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
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

def quarticFourTargetPairResidual
    (W : QuarticFourHighWitness)
    {t : ℝ} (rho : Zeros) (him : (rho : ℂ).im = t) : ℝ :=
  ∑' z : (↑(canonicalTargetPairFinset rho him : Set (SameOrd t)))ᶜ,
    zeroHeightDefect
      (quarticFourPhysicalDetector W.R W.lam W.mu t)
      (t/16)
      ((z : (SameOrd t)) : Zeros)

theorem quarticFourTargetPairResidual_nonneg
    (W : QuarticFourHighWitness)
    {t : ℝ} (ht : 0 < t)
    (hhigh : 8/t < W.eps)
    {rho : Zeros}
    (him : (rho : ℂ).im = t) :
    0 <= quarticFourTargetPairResidual W rho him := by
  unfold quarticFourTargetPairResidual
  apply tsum_nonneg
  intro z
  exact W.zeroHeightDefect_nonneg ht hhigh
    ((z : (SameOrd t)) : Zeros)

theorem quarticFourTargetPairFinset_sum_eq_two_target
    (W : QuarticFourHighWitness)
    {t : ℝ} (ht : 0 < t)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    (∑ z ∈ canonicalTargetPairFinset rho him,
      zeroHeightDefect
        (quarticFourPhysicalDetector W.R W.lam W.mu t)
        (t/16)
        (z : Zeros))
      =
    2 *
      zeroHeightDefect
        (quarticFourPhysicalDetector W.R W.lam W.mu t)
        (t/16) rho := by
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
  have href :
      zeroHeightDefect
        (quarticFourPhysicalDetector W.R W.lam W.mu t)
        (t/16) (z1 : Zeros)
      =
      zeroHeightDefect
        (quarticFourPhysicalDetector W.R W.lam W.mu t)
        (t/16) rho := by
    dsimp [z1]
    unfold zeroHeightDefect
    rw [reflectZero_mult,heightOf_reflectZero,heightDefect_neg_height]
  unfold canonicalTargetPairFinset
  change
    (∑ z ∈ ({z0,z1} : Finset (SameOrd t)),
      zeroHeightDefect
        (quarticFourPhysicalDetector W.R W.lam W.mu t)
        (t/16) (z : Zeros)) = _
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    dsimp [z0]
    rw [href]
    ring
  · simpa [Finset.mem_singleton] using hne

theorem quarticFour_cluster_eq_two_target_add_pairResidual
    (W : QuarticFourHighWitness)
    {t : ℝ} (ht : 0 < t)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    clusterHeightDefect
        (quarticFourPhysicalDetector W.R W.lam W.mu t)
        t (t/16)
      =
    2 *
      zeroHeightDefect
        (quarticFourPhysicalDetector W.R W.lam W.mu t)
        (t/16) rho
      + quarticFourTargetPairResidual W rho him := by
  let f : SameOrd t -> ℝ := fun z =>
    zeroHeightDefect
      (quarticFourPhysicalDetector W.R W.lam W.mu t)
      (t/16) (z : Zeros)
  have hsmooth :=
    quarticFourPhysicalDetector_contDiff
      (t:=t) (lam:=W.lam) (mu:=W.mu) W.Rpos
  have hcompact :=
    quarticFourPhysicalDetector_compact
      (t:=t) (lam:=W.lam) (mu:=W.mu) W.Rpos ht
  have heven :=
    quarticFourPhysicalDetector_even W.R W.lam W.mu t
  have hsum : Summable f :=
    summable_zeroHeightDefect
      hsmooth hcompact heven t (t/16)
  have hsplit :=
    hsum.sum_add_tsum_compl
      (s:=canonicalTargetPairFinset rho him)
  have hcluster :
      clusterHeightDefect
          (quarticFourPhysicalDetector W.R W.lam W.mu t)
          t (t/16)
        = ∑' z : SameOrd t, f z := by
    exact clusterHeightDefect_eq_tsum
      hsmooth hcompact heven t (t/16)
  rw [hcluster, ← hsplit,
      quarticFourTargetPairFinset_sum_eq_two_target W ht him hoff]
  rfl

theorem quarticFour_cluster_ge_two_target
    (W : QuarticFourHighWitness)
    {t : ℝ} (ht : 0 < t)
    (hhigh : 8/t < W.eps)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    2 *
      zeroHeightDefect
        (quarticFourPhysicalDetector W.R W.lam W.mu t)
        (t/16) rho
      <=
    clusterHeightDefect
      (quarticFourPhysicalDetector W.R W.lam W.mu t)
      t (t/16) := by
  rw [quarticFour_cluster_eq_two_target_add_pairResidual
    W ht him hoff]
  exact le_add_of_nonneg_right
    (quarticFourTargetPairResidual_nonneg W ht hhigh him)

theorem quarticFour_cluster_eq_threeProjectiveChannels
    (W : QuarticFourHighWitness)
    {t : ℝ} (ht : 200 <= t) :
    clusterHeightDefect
        (quarticFourPhysicalDetector W.R W.lam W.mu t)
        t (t/16)
      =
    offOrdProjectiveDefect
        (quarticFourPhysicalDetector W.R W.lam W.mu t)
        t (t/16)
      +
    gammaProjectiveDefect
        (quarticFourPhysicalDetector W.R W.lam W.mu t)
        t (t/16)
      +
    poleProjectiveDefect
        (quarticFourPhysicalDetector W.R W.lam W.mu t)
        t (t/16) := by
  have htpos : 0 < t := by linarith
  have hsmooth :=
    quarticFourPhysicalDetector_contDiff
      (t:=t) (lam:=W.lam) (mu:=W.mu) W.Rpos
  have hcompact :=
    quarticFourPhysicalDetector_compact
      (t:=t) (lam:=W.lam) (mu:=W.mu) W.Rpos htpos
  have heven :=
    quarticFourPhysicalDetector_even W.R W.lam W.mu t
  have hshort :=
    quarticFourPhysicalDetector_short_of_twoHundred
      W.Rpos W.RltOne ht
  exact clusterHeightDefect_eq_threeProjectiveChannels
    hsmooth hcompact heven hshort t (t/16)

theorem false_of_quarticFour_external_strict
    (W : QuarticFourHighWitness)
    {t : ℝ} (ht : 200 <= t)
    (hhigh : 8/t < W.eps)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0)
    (hstrict :
      offOrdProjectiveDefect
          (quarticFourPhysicalDetector W.R W.lam W.mu t)
          t (t/16)
        +
      gammaProjectiveDefect
          (quarticFourPhysicalDetector W.R W.lam W.mu t)
          t (t/16)
        +
      poleProjectiveDefect
          (quarticFourPhysicalDetector W.R W.lam W.mu t)
          t (t/16)
        <
      2 *
        zeroHeightDefect
          (quarticFourPhysicalDetector W.R W.lam W.mu t)
          (t/16) rho) :
    False := by
  have htpos : 0 < t := by linarith
  have hlo :=
    quarticFour_cluster_ge_two_target
      W htpos hhigh him hoff
  rw [quarticFour_cluster_eq_threeProjectiveChannels W ht] at hlo
  linarith

end Synthesis
