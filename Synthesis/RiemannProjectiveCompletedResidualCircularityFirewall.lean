import Synthesis.RiemannNormalizedProjectiveSameOrdinateCollapse
import Synthesis.RiemannProjectiveCompletedSmoothResidual

/-!
# Full/off/same-ordinate completed projective accounting

This file marks the exact boundary between useful completed-density cancellation
and a tautological use of the full explicit formula.

The normalized full carrier splits as

  sum'_all A = sum'_{SameOrd(t)} A + sum'_{off} A.

The full explicit formula gives

  (1/(2t)) sum'_all A + 2 SmoothCompleted = 0,

whereas the off-ordinate high consumer is

  (1/(2t)) sum'_off A + 2 SmoothCompleted.

Subtracting yields

  high external residual
    = -(1/(2t)) sum'_{SameOrd(t)} A
    = D_cluster.

Thus pushing the completed-density identity through the full zero formula does
not by itself create a strict upper bound; it recovers the literal cluster
identity.  The prize-facing theorem must estimate the off-ordinate completed
residual independently before this final replacement.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile

/-- Exact partition of the normalized projective full carrier into the target
ordinate fibre and its complement. -/
theorem tsum_full_normalizedProjectiveOffZeroAtom_split_sameOrd
    {t : ℝ} (ht : 18 ≤ t) :
    (∑' rho : Zeros, normalizedProjectiveOffZeroAtom t rho)
      =
    (∑' rho : SameOrd t,
      normalizedProjectiveOffZeroAtom t (rho : Zeros))
      +
    (∑' rho : ((SameOrd t)ᶜ : Set Zeros),
      normalizedProjectiveOffZeroAtom t (rho : Zeros)) := by
  have hfull := normalizedProjectiveOffZeroAtom_summable_full ht
  exact
    (Summable.tsum_add_tsum_compl
      (hfull.subtype (SameOrd t))
      (hfull.subtype ((SameOrd t)ᶜ))).symm

/-- Full normalized zero carrier plus completed smooth density cancels exactly. -/
theorem canonical_fullNormalized_add_completedSmooth_eq_zero
    {t : ℝ} (ht : 18 ≤ t) :
    (1 / (2 * t)) *
      (∑' rho : Zeros,
        normalizedProjectiveOffZeroAtom t rho)
      +
    2 * projectiveRvMCompletedSmoothSignedPair
      (quantitativeCanonicalTaper t)
      t (quantitativeSampleRadius t)
      (canonicalProjectiveCompletedRadius t)
      = 0 := by
  have hzero :=
    canonical_projectiveFullZeroSignedPair_eq_normalizedProjectiveTsum ht
  have hsmooth :=
    canonical_projectiveFullZeroSignedPair_eq_neg_completedSmooth ht
  linarith

/-- Exact subtraction identity: the off-ordinate completed residual is the
negative same-ordinate normalized carrier. -/
theorem canonical_offCompletedResidual_eq_neg_sameOrdNormalized
    {t : ℝ} (ht : 18 ≤ t) :
    (1 / (2 * t)) *
      (∑' rho : ((SameOrd t)ᶜ : Set Zeros),
        normalizedProjectiveOffZeroAtom t (rho : Zeros))
      +
    2 * projectiveRvMCompletedSmoothSignedPair
      (quantitativeCanonicalTaper t)
      t (quantitativeSampleRadius t)
      (canonicalProjectiveCompletedRadius t)
      =
    - (1 / (2 * t)) *
      (∑' rho : SameOrd t,
        normalizedProjectiveOffZeroAtom t (rho : Zeros)) := by
  have ht0 : t ≠ 0 := by linarith
  have hfull :=
    canonical_fullNormalized_add_completedSmooth_eq_zero ht
  have hsplit :=
    tsum_full_normalizedProjectiveOffZeroAtom_split_sameOrd ht
  rw [hsplit] at hfull
  linarith

/-- The completed residual collapse, carried all the way through the full
explicit formula, reproduces the literal positive cluster exactly. -/
theorem canonical_offCompletedResidual_eq_clusterHeightDefect
    {t : ℝ} (ht : 18 ≤ t) :
    (1 / (2 * t)) *
      (∑' rho : ((SameOrd t)ᶜ : Set Zeros),
        normalizedProjectiveOffZeroAtom t (rho : Zeros))
      +
    2 * projectiveRvMCompletedSmoothSignedPair
      (quantitativeCanonicalTaper t)
      t (quantitativeSampleRadius t)
      (canonicalProjectiveCompletedRadius t)
      =
    clusterHeightDefect
      (quantitativeCanonicalTaper t)
      t (quantitativeSampleRadius t) := by
  have ht0 : t ≠ 0 := by linarith
  rw [canonical_offCompletedResidual_eq_neg_sameOrdNormalized ht]
  rw [tsum_sameOrd_normalizedProjectiveOffZeroAtom_eq_neg_two_t_cluster ht]
  field_simp [ht0]
  ring

/-- Same theorem at the named external-residual surface. -/
theorem canonical_projectiveCompletedExternalResidual_eq_cluster
    {t : ℝ} (ht : 18 ≤ t) :
    projectiveCompletedExternalResidual
      (quantitativeCanonicalTaper t)
      t (quantitativeSampleRadius t)
      =
    clusterHeightDefect
      (quantitativeCanonicalTaper t)
      t (quantitativeSampleRadius t) := by
  rw [canonical_projectiveCompletedExternalResidual_eq_normalizedTsum_add_completedSmooth ht]
  exact canonical_offCompletedResidual_eq_clusterHeightDefect ht

end Synthesis
