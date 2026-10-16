import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic
import Synthesis.RiemannG21SupportMomentDomination

/-!
# G21 continuum strictness compiler and fail-closed counterexamples

The pointwise hyperbolic TP2 candidate is not by itself the continuum moment
sign.  The missing analytic ingredient is strict positivity of the symmetrized
double-integral carrier on a positive-measure subset.

This file isolates the exact measure-theoretic strictness compiler and, just as
importantly, records two negative controls:

* a one-atom/degenerate measure collapses every moment-ratio determinant to 0;
* signed weights can reverse the desired orientation even for a strictly-TP2
  two-point kernel.

Hence G21 must really use the companion taper's nonnegative, nondegenerate
positive plateau; neither `TP2` alone nor arbitrary signed test functions may be
promoted into the Clay lane.
-/

noncomputable section

open MeasureTheory Set

namespace Synthesis

/-- A reusable strict-integral compiler.  Nonnegativity plus strict positivity
on any positive-measure subset forces a strictly positive integral. -/
theorem integral_pos_of_nonneg_of_pos_on_posMeasure
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {s : Set α}
    (hf : Integrable f μ)
    (hnonneg : ∀ x, 0 <= f x)
    (hs : 0 < μ s)
    (hpos : ∀ x ∈ s, 0 < f x) :
    0 < ∫ x, f x ∂μ := by
  rw [integral_pos_iff_support_of_nonneg hnonneg hf]
  have hsubset : s ⊆ Function.support f := by
    intro x hx
    exact (hpos x hx).ne'
  exact hs.trans_le (measure_mono hsubset)

/-- The exact final step in the generic TP2-to-moment composition once the
symmetrized double-integral identity and its strict-positive carrier are known. -/
theorem strictMomentCrossProduct_of_symmetrizedCertificate
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : α → ℝ} {s : Set α} {cross : ℝ}
    (hF : Integrable F μ)
    (hFnonneg : ∀ x, 0 <= F x)
    (hs : 0 < μ s)
    (hFpos : ∀ x ∈ s, 0 < F x)
    (hsymm : cross = ((1 : ℝ) / 2) * ∫ x, F x ∂μ) :
    0 < cross := by
  have hint : 0 < ∫ x, F x ∂μ :=
    integral_pos_of_nonneg_of_pos_on_posMeasure hF hFnonneg hs hFpos
  rw [hsymm]
  positivity

/-- Negative control: a single support atom cannot produce a strict moment
ratio separation.  The determinant cancels identically, regardless of the
kernel values. -/
theorem oneAtomMomentDeterminant_zero (ka kp q : ℝ) :
    ka * (q * kp) - (q * ka) * kp = 0 := by
  ring

/-- Concrete signed-weight counterexample.  Start from the strictly-TP2 kernel
matrix

    [1 1]
    [1 2]

whose minor is `1`.  With score `(0,1)` but signed support weights `(1,-1)`,
the low/high weighted moments are `(M0a,MQa,M0p,MQp)=(0,-1,-1,-2)`, and the
wanted cross product is `-1`.  Thus positivity of the taper is structural, not
cosmetic. -/
theorem signedTwoPointWeight_canFlipMomentOrientation :
    ((0 : ℝ) * (-2) - (-1) * (-1)) < 0 := by
  norm_num

/-- The kernel used by the signed-weight counterexample really is strict TP2. -/
theorem signedCounterexampleKernel_isStrictTP2 :
    (1 : ℝ) * 2 - 1 * 1 > 0 := by
  norm_num

/-- Paired no-go receipt: strict TP2 does not imply the desired continuum
moment sign unless the measure/weight assumptions prevent both degeneracy and
sign reversal. -/
theorem tp2_alone_does_not_determine_moment_orientation :
    ((1 : ℝ) * 2 - 1 * 1 > 0) ∧
    (((0 : ℝ) * (-2) - (-1) * (-1)) < 0) := by
  exact ⟨signedCounterexampleKernel_isStrictTP2,
    signedTwoPointWeight_canFlipMomentOrientation⟩

end Synthesis
