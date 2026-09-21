import Synthesis.RiemannProjectiveQuarticBasePoleOrthogonalization
import Synthesis.RiemannProjectiveQuarticTargetPairResidual
import Synthesis.RiemannProjectiveQuarticCompletedResidual

/-!
# Positive-cone base/pole orthogonalized quartic cutset

The three-witness cross-product coefficients cancel the complete q-only
base+Gamma channel and the projective pole channel exactly.  To retain the
same-ordinate target lower bound under that signed linear combination we need
one additional geometric condition: the three coefficients are nonnegative.

Under that positive-cone condition, each individual quartic cluster inequality

  2 D_i(rho) <= Cluster_i

may be multiplied by c_i and summed.  The exact completed-residual identities
then cancel base+Gamma and pole, leaving only the orthogonalized horizontal
carrier.

Thus the high contradiction is reduced to one horizontal-only strict estimate:

  sum_i c_i H_i  <  2 * sum_i c_i D_i(rho).

This is genuinely stronger than the single-detector N-mu route: the two
target-independent scalar channels are projected out before estimation while
the target lower bound survives.

No existence claim for a positive-cone witness triple is made here.  That is
the new finite-dimensional design problem.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile

def quarticBasePoleCombinedTarget
    (W1 W2 W3 : QuarticHighWitness)
    (t : ℝ) (rho : Zeros) : ℝ :=
  quarticBasePoleCoeff1 W1 W2 W3 t *
      zeroHeightDefect (quarticPhysicalDetector W1.R W1.lam t) (t/16) rho
    + quarticBasePoleCoeff2 W1 W2 W3 t *
      zeroHeightDefect (quarticPhysicalDetector W2.R W2.lam t) (t/16) rho
    + quarticBasePoleCoeff3 W1 W2 W3 t *
      zeroHeightDefect (quarticPhysicalDetector W3.R W3.lam t) (t/16) rho

def quarticBasePoleCombinedCluster
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) : ℝ :=
  quarticBasePoleCoeff1 W1 W2 W3 t *
      clusterHeightDefect (quarticPhysicalDetector W1.R W1.lam t) t (t/16)
    + quarticBasePoleCoeff2 W1 W2 W3 t *
      clusterHeightDefect (quarticPhysicalDetector W2.R W2.lam t) t (t/16)
    + quarticBasePoleCoeff3 W1 W2 W3 t *
      clusterHeightDefect (quarticPhysicalDetector W3.R W3.lam t) t (t/16)

def quarticBasePoleCombinedHorizontal
    (W1 W2 W3 : QuarticHighWitness) (t : ℝ) : ℝ :=
  (1/2 : ℝ) *
    (quarticBasePoleCoeff1 W1 W2 W3 t *
        (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          quarticHorizontalSourceTerm W1 t (sigma : Zeros))
      + quarticBasePoleCoeff2 W1 W2 W3 t *
        (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          quarticHorizontalSourceTerm W2 t (sigma : Zeros))
      + quarticBasePoleCoeff3 W1 W2 W3 t *
        (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          quarticHorizontalSourceTerm W3 t (sigma : Zeros)))

theorem quarticBasePoleCombinedCluster_eq_horizontal
    (W1 W2 W3 : QuarticHighWitness)
    {t : ℝ} (ht : 100 <= t) :
    quarticBasePoleCombinedCluster W1 W2 W3 t
      =
    quarticBasePoleCombinedHorizontal W1 W2 W3 t := by
  have h1 := quartic_cluster_eq_baseMu_add_horizontal_add_pole W1 ht
  have h2 := quartic_cluster_eq_baseMu_add_horizontal_add_pole W2 ht
  have h3 := quartic_cluster_eq_baseMu_add_horizontal_add_pole W3 ht
  unfold quarticBasePoleCombinedCluster
    quarticBasePoleCombinedHorizontal
    quarticPoleResidual
  have hbase := quarticBasePoleCoeffs_cancel_base W1 W2 W3 t
  have hpole := quarticBasePoleCoeffs_cancel_pole W1 W2 W3 t
  rw [h1, h2, h3]
  ring_nf at hbase hpole ⊢
  linarith

theorem two_mul_combinedTarget_le_combinedCluster
    (W1 W2 W3 : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    (hhigh1 : 8/t < W1.eps)
    (hhigh2 : 8/t < W2.eps)
    (hhigh3 : 8/t < W3.eps)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0)
    (hc1 : 0 <= quarticBasePoleCoeff1 W1 W2 W3 t)
    (hc2 : 0 <= quarticBasePoleCoeff2 W1 W2 W3 t)
    (hc3 : 0 <= quarticBasePoleCoeff3 W1 W2 W3 t) :
    2 * quarticBasePoleCombinedTarget W1 W2 W3 t rho
      <=
    quarticBasePoleCombinedCluster W1 W2 W3 t := by
  have h1 := quartic_cluster_ge_two_target W1 ht hhigh1 him hoff
  have h2 := quartic_cluster_ge_two_target W2 ht hhigh2 him hoff
  have h3 := quartic_cluster_ge_two_target W3 ht hhigh3 him hoff
  have h1' := mul_le_mul_of_nonneg_left h1 hc1
  have h2' := mul_le_mul_of_nonneg_left h2 hc2
  have h3' := mul_le_mul_of_nonneg_left h3 hc3
  unfold quarticBasePoleCombinedTarget quarticBasePoleCombinedCluster
  linarith

/--
Prize-facing positive-cone cutset.  Once the complete base+Gamma and pole
channels are exactly projected out, a strict horizontal upper below the
combined doubled target is contradictory.
-/
theorem false_of_quarticBasePole_positiveCone_horizontal_strict
    (W1 W2 W3 : QuarticHighWitness)
    {t : ℝ} (ht : 100 <= t)
    (hhigh1 : 8/t < W1.eps)
    (hhigh2 : 8/t < W2.eps)
    (hhigh3 : 8/t < W3.eps)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0)
    (hc1 : 0 <= quarticBasePoleCoeff1 W1 W2 W3 t)
    (hc2 : 0 <= quarticBasePoleCoeff2 W1 W2 W3 t)
    (hc3 : 0 <= quarticBasePoleCoeff3 W1 W2 W3 t)
    (hstrict :
      quarticBasePoleCombinedHorizontal W1 W2 W3 t
        <
      2 * quarticBasePoleCombinedTarget W1 W2 W3 t rho) :
    False := by
  have htpos : 0 < t := by linarith
  have hlo :=
    two_mul_combinedTarget_le_combinedCluster
      W1 W2 W3 htpos hhigh1 hhigh2 hhigh3
      him hoff hc1 hc2 hc3
  rw [quarticBasePoleCombinedCluster_eq_horizontal W1 W2 W3 ht] at hlo
  linarith


/--
Under the positive cone, a nonzero base/pole target determinant forces the
combined target signal to be strictly positive for every off-line target in the
common high band.
-/
theorem quarticBasePoleCombinedTarget_pos_of_det_ne_zero
    (W1 W2 W3 : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t)
    (hhigh1 : 8/t < W1.eps)
    (hhigh2 : 8/t < W2.eps)
    (hhigh3 : 8/t < W3.eps)
    (rho : Zeros)
    (hoff : heightOf rho ≠ 0)
    (hc1 : 0 <= quarticBasePoleCoeff1 W1 W2 W3 t)
    (hc2 : 0 <= quarticBasePoleCoeff2 W1 W2 W3 t)
    (hc3 : 0 <= quarticBasePoleCoeff3 W1 W2 W3 t)
    (hdet : quarticBasePoleTargetDet W1 W2 W3 t ≠ 0) :
    0 < quarticBasePoleCombinedTarget W1 W2 W3 t rho := by
  have hD1 := W1.zeroHeightDefect_pos_of_offLine ht hhigh1 rho hoff
  have hD2 := W2.zeroHeightDefect_pos_of_offLine ht hhigh2 rho hoff
  have hD3 := W3.zeroHeightDefect_pos_of_offLine ht hhigh3 rho hoff
  have hsome :
      0 < quarticBasePoleCoeff1 W1 W2 W3 t
        ∨ 0 < quarticBasePoleCoeff2 W1 W2 W3 t
        ∨ 0 < quarticBasePoleCoeff3 W1 W2 W3 t := by
    by_contra h
    push_neg at h
    have h1 : quarticBasePoleCoeff1 W1 W2 W3 t = 0 :=
      le_antisymm h.1 hc1
    have h2 : quarticBasePoleCoeff2 W1 W2 W3 t = 0 :=
      le_antisymm h.2.1 hc2
    have h3 : quarticBasePoleCoeff3 W1 W2 W3 t = 0 :=
      le_antisymm h.2.2 hc3
    apply hdet
    unfold quarticBasePoleTargetDet
    rw [h1,h2,h3]
    ring
  unfold quarticBasePoleCombinedTarget
  rcases hsome with h1 | h2 | h3
  · have h1D : 0 < quarticBasePoleCoeff1 W1 W2 W3 t *
        zeroHeightDefect (quarticPhysicalDetector W1.R W1.lam t) (t/16) rho :=
      mul_pos h1 hD1
    have h2D : 0 <= quarticBasePoleCoeff2 W1 W2 W3 t *
        zeroHeightDefect (quarticPhysicalDetector W2.R W2.lam t) (t/16) rho :=
      mul_nonneg hc2 hD2.le
    have h3D : 0 <= quarticBasePoleCoeff3 W1 W2 W3 t *
        zeroHeightDefect (quarticPhysicalDetector W3.R W3.lam t) (t/16) rho :=
      mul_nonneg hc3 hD3.le
    linarith
  · have h1D : 0 <= quarticBasePoleCoeff1 W1 W2 W3 t *
        zeroHeightDefect (quarticPhysicalDetector W1.R W1.lam t) (t/16) rho :=
      mul_nonneg hc1 hD1.le
    have h2D : 0 < quarticBasePoleCoeff2 W1 W2 W3 t *
        zeroHeightDefect (quarticPhysicalDetector W2.R W2.lam t) (t/16) rho :=
      mul_pos h2 hD2
    have h3D : 0 <= quarticBasePoleCoeff3 W1 W2 W3 t *
        zeroHeightDefect (quarticPhysicalDetector W3.R W3.lam t) (t/16) rho :=
      mul_nonneg hc3 hD3.le
    linarith
  · have h1D : 0 <= quarticBasePoleCoeff1 W1 W2 W3 t *
        zeroHeightDefect (quarticPhysicalDetector W1.R W1.lam t) (t/16) rho :=
      mul_nonneg hc1 hD1.le
    have h2D : 0 <= quarticBasePoleCoeff2 W1 W2 W3 t *
        zeroHeightDefect (quarticPhysicalDetector W2.R W2.lam t) (t/16) rho :=
      mul_nonneg hc2 hD2.le
    have h3D : 0 < quarticBasePoleCoeff3 W1 W2 W3 t *
        zeroHeightDefect (quarticPhysicalDetector W3.R W3.lam t) (t/16) rho :=
      mul_pos h3 hD3
    linarith

end Synthesis
