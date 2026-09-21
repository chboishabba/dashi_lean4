import Synthesis.RiemannNormalizedProjectiveBaseCarrierCollapse
import Synthesis.RiemannNormalizedProjectiveHorizontalPhaseOneBand
import Synthesis.RiemannProjectiveCompletedSmoothResidual
import Synthesis.RiemannProjectiveFullCompletedCancellation

/-!
# Completed-base high residual after signed horizontal cancellation

The q-only projective base carrier is unchanged by deleting SameOrd(t), while
the horizontal source carries all target-fibre deletion geometry.

Define the completed base residual

  R_base(t)
    = (1/(2t)) * sum'_all B_sigma(t)
      + 2 * SmoothCompleted(t).

Then the exact canonical high residual is

  R_high(t)
    = R_base(t)
      + (1/(2t)) * sum'_off H_sigma(t).

Inside any phase-one cutoff the finite horizontal middle is nonpositive, so

  R_high(t)
    <= R_base(t) + (K/(2t)) farShellBound(A,|t|,J).

This is a genuinely prize-facing one-sided compiler: no finite local horizontal
carrier remains.

The second theorem is an accounting audit, not an estimate.  Full completed
cancellation and the full atom base+horizontal split imply

  R_base(t) = -(1/(2t)) * sum'_all H_sigma(t).

Thus the remaining completed-base sign problem is exactly a signed theorem on
the full horizontal carrier.  Substituting this identity together with the
off-carrier identity all the way through would recover the same-ordinate
cluster tautologically; it must not be mistaken for the required strict bound.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.FarShellCutoffTailBound

def canonicalCompletedBaseResidual (t : ℝ) : ℝ :=
  (1 / (2 * t)) *
    (∑' rho : Zeros,
      normalizedProjectiveBaseSourceTerm t rho)
    +
  2 * projectiveRvMCompletedSmoothSignedPair
    (quantitativeCanonicalTaper t)
    t (quantitativeSampleRadius t)
    (canonicalProjectiveCompletedRadius t)

/-- Exact completed high residual split into the full-carrier q-only base
residual plus the off-ordinate horizontal tsum. -/
theorem canonicalOffCompletedResidual_eq_completedBase_add_offHorizontal
    {t : ℝ} (ht : 18 ≤ t) :
    canonicalOffCompletedResidual t
      =
    canonicalCompletedBaseResidual t
      +
    (1 / (2 * t)) *
      (∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        normalizedProjectiveHorizontalSourceTerm t (sigma : Zeros)) := by
  unfold canonicalOffCompletedResidual canonicalCompletedBaseResidual
  rw [tsum_offOrd_normalizedProjectiveAtom_eq_base_add_horizontal ht]
  rw [← tsum_full_normalizedProjectiveBaseSourceTerm_eq_offOrd ht]
  ring

/--
Prize-facing signed-band upper compiler.

For any natural cutoff in the exact phase-one monotonicity window, the complete
canonical high residual is bounded by the completed base residual plus only the
far-shell horizontal charge.
-/
theorem exists_canonicalOffCompletedResidual_le_base_add_farShell
    {t : ℝ} (ht : 18 ≤ t)
    {J : ℕ} (hJ : 1 ≤ J)
    (hJphase :
      (J : ℝ) * (9 * Real.pi / (4 * t)) < 1) :
    ∃ A K : ℝ, 1 ≤ A ∧ 0 ≤ K ∧
      canonicalOffCompletedResidual t
        ≤
      canonicalCompletedBaseResidual t
        + (1 / (2 * t)) * (K * farShellBound A |t| J) := by
  obtain ⟨A, K, hA, hK, hhoriz⟩ :=
    exists_offOrdProjectiveHorizontal_le_farShell_of_cutoff_phase_one
      ht hJ hJphase
  have hcoef : 0 ≤ 1 / (2 * t) := by positivity
  have hscaled :=
    mul_le_mul_of_nonneg_left hhoriz hcoef
  refine ⟨A, K, hA, hK, ?_⟩
  rw [canonicalOffCompletedResidual_eq_completedBase_add_offHorizontal ht]
  exact add_le_add_left hscaled _

/--
Exact audit identity: the completed q-only base residual is the negative full
horizontal carrier.

This is useful for locating the mathematical wall, but is not itself a strict
estimate.
-/
theorem canonicalCompletedBaseResidual_eq_neg_fullHorizontal
    {t : ℝ} (ht : 18 ≤ t) :
    canonicalCompletedBaseResidual t
      =
    - (1 / (2 * t)) *
      (∑' rho : Zeros,
        normalizedProjectiveHorizontalSourceTerm t rho) := by
  have ht0 : t ≠ 0 := by linarith
  have hfull :=
    canonical_fullNormalized_add_completedSmooth_eq_zero ht
  have hsplit :
      (∑' rho : Zeros,
        normalizedProjectiveOffZeroAtom t rho)
        =
      (∑' rho : Zeros,
        normalizedProjectiveBaseSourceTerm t rho)
        +
      (∑' rho : Zeros,
        normalizedProjectiveHorizontalSourceTerm t rho) := by
    have hbase :=
      normalizedProjectiveBaseSourceTerm_summable_full ht
    have hhoriz :=
      normalizedProjectiveHorizontalSourceTerm_summable_full ht
    rw [← hbase.tsum_add hhoriz]
    apply tsum_congr
    intro rho
    exact
      normalizedProjectiveOffZeroAtom_eq_baseSource_add_horizontalSource
        ht0 rho
  rw [hsplit] at hfull
  unfold canonicalCompletedBaseResidual
  linarith

end Synthesis
