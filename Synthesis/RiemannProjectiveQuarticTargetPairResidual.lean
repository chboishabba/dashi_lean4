import Synthesis.RiemannProjectiveQuarticHighCluster
import Synthesis.RiemannCanonicalTargetPairResidual

/-!
# Exact target-pair residual for the high quartic detector

The signed quartic profile is not GateData, but at sufficiently high ordinate
its local quartic target band contains the entire critical strip after the
r=t/16 normalization.  Therefore every same-ordinate defect is nonnegative.

For a hypothetical off-line target rho at ordinate t, reflection supplies the
distinct partner reflectZero rho with the same defect.  Splitting those two
points from the same-ordinate tsum gives exactly

  D_cluster^Q = 2 D_rho^Q + R_pair^Q,

with R_pair^Q >= 0.

This restores the target-pair contradiction architecture for the signed
quartic detector.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

def quarticTargetPairResidual
    (W : QuarticHighWitness)
    {t : ℝ} (rho : Zeros) (him : (rho : ℂ).im = t) : ℝ :=
  ∑' z : (↑(canonicalTargetPairFinset rho him : Set (SameOrd t)))ᶜ,
    zeroHeightDefect
      (quarticPhysicalDetector W.R W.lam t)
      (t/16)
      ((z : (SameOrd t)) : Zeros)

theorem quarticTargetPairFinset_sum_eq_two_target
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    (∑ z ∈ canonicalTargetPairFinset rho him,
      zeroHeightDefect
        (quarticPhysicalDetector W.R W.lam t)
        (t/16)
        (z : Zeros))
      =
    2 *
      zeroHeightDefect
        (quarticPhysicalDetector W.R W.lam t)
        (t/16)
        rho := by
  let z0 : SameOrd t := ⟨rho, him⟩
  let z1 : SameOrd t :=
    ⟨reflectZero rho, by
      rw [im_reflectZero]
      exact him⟩
  have hne : z1 ≠ z0 := by
    intro h
    have hv : (z1 : Zeros) = (z0 : Zeros) := congrArg Subtype.val h
    dsimp [z0,z1] at hv
    exact (reflectZero_ne_of_height_ne_zero hoff) hv
  have href :
      zeroHeightDefect
        (quarticPhysicalDetector W.R W.lam t)
        (t/16)
        (z1 : Zeros)
        =
      zeroHeightDefect
        (quarticPhysicalDetector W.R W.lam t)
        (t/16)
        rho := by
    dsimp [z1]
    unfold zeroHeightDefect
    rw [reflectZero_mult, heightOf_reflectZero,
      heightDefect_neg_height]
  unfold canonicalTargetPairFinset
  change
    (∑ z ∈ ({z0,z1} : Finset (SameOrd t)),
      zeroHeightDefect
        (quarticPhysicalDetector W.R W.lam t)
        (t/16)
        (z : Zeros))
      = _
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    dsimp [z0]
    rw [href]
    ring
  · simpa [Finset.mem_singleton] using hne

theorem quarticTargetPairResidual_nonneg
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    (hhigh : 8/t < W.eps)
    {rho : Zeros}
    (him : (rho : ℂ).im = t) :
    0 ≤ quarticTargetPairResidual W rho him := by
  unfold quarticTargetPairResidual
  apply tsum_nonneg
  intro z
  exact W.zeroHeightDefect_nonneg ht hhigh
    ((z : (SameOrd t)) : Zeros)

theorem quartic_cluster_eq_two_target_add_pairResidual
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    clusterHeightDefect
        (quarticPhysicalDetector W.R W.lam t)
        t (t/16)
      =
    2 *
      zeroHeightDefect
        (quarticPhysicalDetector W.R W.lam t)
        (t/16)
        rho
      +
    quarticTargetPairResidual W rho him := by
  let f : SameOrd t → ℝ := fun z =>
    zeroHeightDefect
      (quarticPhysicalDetector W.R W.lam t)
      (t/16)
      (z : Zeros)
  have hsmooth :
      ContDiff ℝ 2 (quarticPhysicalDetector W.R W.lam t) :=
    quarticPhysicalDetector_contDiff W.Rpos
  have hcompact :
      HasCompactSupport (quarticPhysicalDetector W.R W.lam t) :=
    quarticPhysicalDetector_compact W.Rpos ht
  have heven :
      ∀ u,
        quarticPhysicalDetector W.R W.lam t (-u)
          =
        quarticPhysicalDetector W.R W.lam t u :=
    quarticPhysicalDetector_even W.R W.lam t
  have hsum : Summable f :=
    summable_zeroHeightDefect
      hsmooth hcompact heven t (t/16)
  have hsplit :=
    hsum.sum_add_tsum_compl
      (s := canonicalTargetPairFinset rho him)
  have hcluster :
      clusterHeightDefect
          (quarticPhysicalDetector W.R W.lam t)
          t (t/16)
        =
      ∑' z : SameOrd t, f z := by
    exact clusterHeightDefect_eq_tsum
      hsmooth hcompact heven t (t/16)
  rw [hcluster, ← hsplit,
      quarticTargetPairFinset_sum_eq_two_target W ht him hoff]
  rfl

theorem quartic_cluster_ge_two_target
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    (hhigh : 8/t < W.eps)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    2 *
      zeroHeightDefect
        (quarticPhysicalDetector W.R W.lam t)
        (t/16)
        rho
      ≤
    clusterHeightDefect
      (quarticPhysicalDetector W.R W.lam t)
      t (t/16) := by
  rw [quartic_cluster_eq_two_target_add_pairResidual W ht him hoff]
  exact le_add_of_nonneg_right
    (quarticTargetPairResidual_nonneg W ht hhigh him)

end Synthesis
