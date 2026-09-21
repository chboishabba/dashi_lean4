import Synthesis.RiemannProjectiveQuarticOffInfiniteSplit
import Synthesis.RiemannProjectiveCompletedSmoothResidual
import Synthesis.RiemannProjectiveQuarticHighCutset

/-!
# Completed smooth-density accounting for the quartic escape detector

The quartic signed taper changes the local q-kernel geometry, but it does not
change the explicit-formula accounting: Gamma is still exactly the mu pairing
and the pole is still exactly the Pi_X pairing on the same projective test.

This file prevents a false conclusion from the raw negative zero window.
The O(t log t) negative zero mass in a macroscopic quartic band is paired with
an O(t log t) smooth mu mass of the opposite explicit-formula sign.  The
primitive object is therefore again a completed discrepancy, not the raw zero
sum.

For the physical quartic detector g_t and r=t/16:

  external_Q
    = 1/2 sum'_all B_sigma^Q
      + 1/2 sum'_off H_sigma^Q
      + 2 <k_Q, -(mu+Pi_X)>.

Equivalently, the base+Gamma part is the signed zero-minus-mu pairing for the
quartic q-kernel.  The quartic negative lobe improves the geometry of this
pairing, but does not create a free density-level negative margin.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

def quarticCompletedRadius (t : ℝ) : ℝ :=
  16 * (Real.pi/2 + 1) / t

theorem quarticCompletedRadius_pos
    {t : ℝ} (ht : 0 < t) :
    0 < quarticCompletedRadius t := by
  unfold quarticCompletedRadius
  positivity

theorem quarticPhysicalDetector_support_completedRadius
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t) :
    ∀ u,
      quarticPhysicalDetector W.R W.lam t u ≠ 0 ->
      |u| <= quarticCompletedRadius t := by
  intro u hu
  exact
    (physicalQuarticProfile_support_abs_lt
      W.Rpos W.RltOne ht hu).le

def quarticBaseMuResidual
    (W : QuarticHighWitness) (t : ℝ) : ℝ :=
  (1/2 : ℝ) *
    (∑' sigma : Zeros, quarticBaseSourceTerm W t sigma)
  + 2 * projectiveRvMMuSignedPair
      (quarticPhysicalDetector W.R W.lam t)
      t (t/16)

def quarticCompletedExternalResidual
    (W : QuarticHighWitness) (t : ℝ) : ℝ :=
  offOrdProjectiveDefect
      (quarticPhysicalDetector W.R W.lam t)
      t (t/16)
    + gammaProjectiveDefect
      (quarticPhysicalDetector W.R W.lam t)
      t (t/16)
    + poleProjectiveDefect
      (quarticPhysicalDetector W.R W.lam t)
      t (t/16)

/--
Exact quartic external split into the full-carrier base+mu discrepancy, the
off-ordinate horizontal carrier, and the literal pole defect.
-/
theorem quarticCompletedExternalResidual_eq_baseMu_add_horizontal_add_pole
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t) :
    quarticCompletedExternalResidual W t
      =
    quarticBaseMuResidual W t
      + (1/2 : ℝ) *
        (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          quarticHorizontalSourceTerm W t (sigma : Zeros))
      + poleProjectiveDefect
          (quarticPhysicalDetector W.R W.lam t)
          t (t/16) := by
  unfold quarticCompletedExternalResidual quarticBaseMuResidual
  rw [quartic_offOrdProjectiveDefect_eq_base_add_horizontal W ht]
  rw [← tsum_full_quarticBase_eq_offOrd W ht]
  rw [gammaProjectiveDefect_eq_two_projectiveRvMMuSignedPair
      (quarticPhysicalDetector_contDiff W.Rpos)
      (quarticPhysicalDetector_even W.R W.lam t)
      (quarticPhysicalDetector_support_completedRadius W ht)
      (quarticCompletedRadius_pos ht).le
      t (t/16)]
  ring

/--
Completed-density form: Gamma and pole are one smooth pairing even for the
signed quartic detector.
-/
theorem quarticCompletedExternalResidual_eq_off_add_completedSmooth
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 0 < t) :
    quarticCompletedExternalResidual W t
      =
    offOrdProjectiveDefect
        (quarticPhysicalDetector W.R W.lam t)
        t (t/16)
      + 2 *
        projectiveRvMCompletedSmoothSignedPair
          (quarticPhysicalDetector W.R W.lam t)
          t (t/16) (quarticCompletedRadius t) := by
  unfold quarticCompletedExternalResidual
  exact projectiveCompletedExternalResidual_eq_off_add_completedSmooth
    (quarticPhysicalDetector_contDiff W.Rpos)
    (quarticPhysicalDetector_compact W.Rpos ht)
    (quarticPhysicalDetector_even W.R W.lam t)
    (quarticPhysicalDetector_support_completedRadius W ht)
    (quarticCompletedRadius_pos ht)
    t (t/16)

/--
Prize-facing exact cluster identity in completed quartic variables.
-/
theorem quartic_cluster_eq_baseMu_add_horizontal_add_pole
    (W : QuarticHighWitness)
    {t : ℝ} (ht : 100 <= t) :
    clusterHeightDefect
        (quarticPhysicalDetector W.R W.lam t)
        t (t/16)
      =
    quarticBaseMuResidual W t
      + (1/2 : ℝ) *
        (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
          quarticHorizontalSourceTerm W t (sigma : Zeros))
      + poleProjectiveDefect
          (quarticPhysicalDetector W.R W.lam t)
          t (t/16) := by
  have htpos : 0 < t := by linarith
  rw [quartic_cluster_eq_threeProjectiveChannels W ht]
  change quarticCompletedExternalResidual W t = _
  exact
    quarticCompletedExternalResidual_eq_baseMu_add_horizontal_add_pole
      W htpos

end Synthesis
