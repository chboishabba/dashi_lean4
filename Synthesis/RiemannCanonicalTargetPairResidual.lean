import Synthesis.RiemannCanonicalCompletedBaseResidual
import Synthesis.RiemannReflectionDoubledProjectiveGate

/-!
# Exact target-pair residual on the same-ordinate fibre

For an off-line target rho at ordinate t, let z0=rho and z1=reflectZero rho in
SameOrd(t).  GateData makes every same-ordinate height defect nonnegative, and
reflection gives D(z1)=D(z0).

Hence the literal cluster admits the exact decomposition

  D_cluster
    = 2 D_rho
      + sum'_{z notin {rho,reflect rho}} D_z.

The residual tsum is nonnegative.  Since the canonical completed high residual
is exactly D_cluster, the distance from the desired strict cut is therefore not
an unspecified external budget:

  R_high(t) - 2 D_rho
    = sum'_{same ordinate, excluding target pair} D_z >= 0.

This is the exact target-relative endgame variable.  Any prize-facing analytic
upper estimate must force this literal residual below zero under the off-line
hypothesis; estimates that merely shrink target-independent absolute budgets do
not address the remaining theorem.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate

def canonicalTargetPairFinset
    {t : ℝ} (rho : Zeros) (him : (rho : ℂ).im = t) :
    Finset (SameOrd t) :=
  {⟨rho, him⟩,
   ⟨reflectZero rho, by
      rw [Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair.im_reflectZero]
      exact him⟩}

def canonicalTargetPairResidual
    {t : ℝ} (rho : Zeros) (him : (rho : ℂ).im = t) : ℝ :=
  ∑' z : (↑(canonicalTargetPairFinset rho him : Set (SameOrd t)))ᶜ,
    zeroHeightDefect
      (quantitativeCanonicalTaper t)
      (quantitativeSampleRadius t)
      ((z : (SameOrd t)) : Zeros)

theorem canonicalTargetPairFinset_sum_eq_two_target
    {t : ℝ} (ht : 18 ≤ t)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    (∑ z ∈ canonicalTargetPairFinset rho him,
      zeroHeightDefect
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t)
        (z : Zeros))
      =
    2 *
      zeroHeightDefect
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t)
        rho := by
  let z0 : SameOrd t := ⟨rho, him⟩
  let z1 : SameOrd t :=
    ⟨reflectZero rho, by
      rw [Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair.im_reflectZero]
      exact him⟩
  have hne : z1 ≠ z0 := by
    intro h
    have hv : (z1 : Zeros) = (z0 : Zeros) := congrArg Subtype.val h
    dsimp [z0, z1] at hv
    exact (reflectZero_ne_of_height_ne_zero hoff) hv
  have href :
      zeroHeightDefect
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t)
        (z1 : Zeros)
        =
      zeroHeightDefect
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t)
        rho := by
    dsimp [z1]
    unfold zeroHeightDefect
    rw [Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair.reflectZero_mult,
        Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair.heightOf_reflectZero,
        Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector.heightDefect_neg_height]
  unfold canonicalTargetPairFinset
  change
    (∑ z ∈ ({z0, z1} : Finset (SameOrd t)),
      zeroHeightDefect
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t)
        (z : Zeros))
      = _
  rw [Finset.sum_insert]
  · rw [Finset.sum_singleton]
    dsimp [z0]
    rw [href]
    ring
  · simpa [Finset.mem_singleton] using hne

theorem canonicalTargetPairResidual_nonneg
    {t : ℝ} (ht : 18 ≤ t)
    {rho : Zeros}
    (him : (rho : ℂ).im = t) :
    0 ≤ canonicalTargetPairResidual rho him := by
  unfold canonicalTargetPairResidual
  apply tsum_nonneg
  intro z
  exact zeroHeightDefect_nonneg
    (quantitativeCanonicalGateData ht).smooth.continuous
    (quantitativeCanonicalGateData ht).compactSupport
    (quantitativeCanonicalGateData ht).nonneg
    (quantitativeCanonicalGateData ht).radiusPos
    (quantitativeCanonicalGateData ht).radial
    ((z : (SameOrd t)) : Zeros)

/--
Exact target-pair subtraction from the literal same-ordinate cluster.
-/
theorem canonical_cluster_eq_two_target_add_pairResidual
    {t : ℝ} (ht : 18 ≤ t)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    clusterHeightDefect
        (quantitativeCanonicalTaper t)
        t (quantitativeSampleRadius t)
      =
    2 *
      zeroHeightDefect
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t)
        rho
      +
    canonicalTargetPairResidual rho him := by
  let f : SameOrd t → ℝ := fun z =>
    zeroHeightDefect
      (quantitativeCanonicalTaper t)
      (quantitativeSampleRadius t)
      (z : Zeros)
  have hsum : Summable f :=
    summable_zeroHeightDefect
      (quantitativeCanonicalTaper_contDiff ht)
      (quantitativeCanonicalTaper_compact ht)
      quantitativeCanonicalTaper_even
      t (quantitativeSampleRadius t)
  have hsplit :=
    hsum.sum_add_tsum_compl (s := canonicalTargetPairFinset rho him)
  have hcluster :
      clusterHeightDefect
          (quantitativeCanonicalTaper t)
          t (quantitativeSampleRadius t)
        =
      ∑' z : SameOrd t, f z := by
    exact clusterHeightDefect_eq_tsum
      (quantitativeCanonicalTaper_contDiff ht)
      (quantitativeCanonicalTaper_compact ht)
      quantitativeCanonicalTaper_even
      t (quantitativeSampleRadius t)
  rw [hcluster]
  rw [← hsplit]
  rw [canonicalTargetPairFinset_sum_eq_two_target ht him hoff]
  rfl

/--
The exact completed high residual minus the doubled target is the nonnegative
pair-removed same-ordinate residual.
-/
theorem canonicalOffCompletedResidual_sub_two_target_eq_pairResidual
    {t : ℝ} (ht : 18 ≤ t)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    canonicalOffCompletedResidual t
      -
    2 *
      zeroHeightDefect
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t)
        rho
      =
    canonicalTargetPairResidual rho him := by
  rw [canonicalOffCompletedResidual_eq_cluster ht,
      canonical_cluster_eq_two_target_add_pairResidual ht him hoff]
  ring

theorem canonicalOffCompletedResidual_sub_two_target_nonneg
    {t : ℝ} (ht : 18 ≤ t)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    0 ≤
      canonicalOffCompletedResidual t
        -
      2 *
        zeroHeightDefect
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t)
          rho := by
  rw [canonicalOffCompletedResidual_sub_two_target_eq_pairResidual
    ht him hoff]
  exact canonicalTargetPairResidual_nonneg ht him

end Synthesis
