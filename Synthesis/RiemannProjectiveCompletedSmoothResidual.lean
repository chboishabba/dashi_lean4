import Synthesis.RiemannProjectiveRvMPiXPoleSameObject
import Synthesis.RiemannNormalizedProjectiveOffTsumAttachment
import Synthesis.RiemannCanonicalGateData
import Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

/-!
# Completed projective smooth density: mu + Pi_X

The Gamma and pole channels are not independent external budgets on the literal
projective consumer.  Zeta23 identifies them with the same projective test paired
against the two smooth densities

  mu(tau),  Pi_X(tau).

This file packages those two densities before any estimate and rewrites the
canonical high cluster exactly as

  D_cluster
    = (1/(2t)) * sum' A_rho^proj
      + 2 * <k_proj, -(mu + Pi_X)>_Re.

Thus the primitive high-side counting object is the zero carrier relative to the
completed smooth density.  A later base/horizontal split may refine the zero
carrier, but Gamma and pole must not be charged again as separate positive
budgets.

No estimate enters here.
-/

noncomputable section

open MeasureTheory Complex Set
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition

/-- Signed pairing of the exact projective test against the completed smooth
RvM/pole density mu + Pi_X. -/
def projectiveRvMCompletedSmoothSignedPair
    (g : ℝ → ℝ) (t r L : ℝ) : ℝ :=
  projectiveRvMMuSignedPair g t r
    + projectiveRvMPiXSignedPair g t r L

/-- The three literal external channels, before using the Gamma/Pi_X
same-object theorems. -/
def projectiveCompletedExternalResidual
    (g : ℝ → ℝ) (t r : ℝ) : ℝ :=
  offOrdProjectiveDefect g t r
    + gammaProjectiveDefect g t r
    + poleProjectiveDefect g t r

/-- Exact completed-density collapse of Gamma + pole on the projective
consumer. -/
theorem projectiveCompletedExternalResidual_eq_off_add_completedSmooth
    {g : ℝ → ℝ} {L : ℝ}
    (hgs : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g)
    (heven : ∀ u, g (-u) = g u)
    (hsupp : ∀ u, g u ≠ 0 -> |u| ≤ L)
    (hL : 0 < L)
    (t r : ℝ) :
    projectiveCompletedExternalResidual g t r
      =
    offOrdProjectiveDefect g t r
      + 2 * projectiveRvMCompletedSmoothSignedPair g t r L := by
  unfold projectiveCompletedExternalResidual
    projectiveRvMCompletedSmoothSignedPair
  rw [gammaProjectiveDefect_eq_two_projectiveRvMMuSignedPair
      hgs heven hsupp hL.le t r,
    poleProjectiveDefect_eq_two_projectiveRvMPiXSignedPair
      hgs hgc heven hsupp hL t r]
  ring

/-- Canonical support radius used as the literal Pi_X cutoff. -/
def canonicalProjectiveCompletedRadius (t : ℝ) : ℝ :=
  9 * Real.pi / (4 * t)

theorem canonicalProjectiveCompletedRadius_pos
    {t : ℝ} (ht : 18 ≤ t) :
    0 < canonicalProjectiveCompletedRadius t := by
  unfold canonicalProjectiveCompletedRadius
  positivity

/-- The canonical taper is supported in the completed-density cutoff. -/
theorem quantitativeCanonicalTaper_support_completedRadius
    {t : ℝ} (ht : 18 ≤ t) :
    ∀ u, quantitativeCanonicalTaper t u ≠ 0 ->
      |u| ≤ canonicalProjectiveCompletedRadius t := by
  intro u hu
  exact (quantitativeCanonicalTaper_support_abs_lt ht hu).le

/-- Exact canonical external residual on the normalized projective zero carrier
and completed smooth density. -/
theorem canonical_projectiveCompletedExternalResidual_eq_normalizedTsum_add_completedSmooth
    {t : ℝ} (ht : 18 ≤ t) :
    projectiveCompletedExternalResidual
        (quantitativeCanonicalTaper t)
        t (quantitativeSampleRadius t)
      =
    (1 / (2 * t)) *
      ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        normalizedProjectiveOffZeroAtom t (sigma : Zeros)
      +
    2 * projectiveRvMCompletedSmoothSignedPair
      (quantitativeCanonicalTaper t)
      t (quantitativeSampleRadius t)
      (canonicalProjectiveCompletedRadius t) := by
  rw [projectiveCompletedExternalResidual_eq_off_add_completedSmooth
      (quantitativeCanonicalTaper_contDiff ht)
      (quantitativeCanonicalTaper_compact ht)
      quantitativeCanonicalTaper_even
      (quantitativeCanonicalTaper_support_completedRadius ht)
      (canonicalProjectiveCompletedRadius_pos ht)
      t (quantitativeSampleRadius t)]
  rw [canonical_offOrdProjectiveDefect_eq_normalizedProjectiveTsum ht]

/-- The short-support literal balance can now be stated directly with the
completed smooth density; Gamma and pole no longer appear as primitive debts. -/
theorem canonical_clusterHeightDefect_eq_normalizedTsum_add_completedSmooth
    {t : ℝ} (ht : 18 ≤ t) :
    clusterHeightDefect
        (quantitativeCanonicalTaper t)
        t (quantitativeSampleRadius t)
      =
    (1 / (2 * t)) *
      ∑' sigma : ((SameOrd t)ᶜ : Set Zeros),
        normalizedProjectiveOffZeroAtom t (sigma : Zeros)
      +
    2 * projectiveRvMCompletedSmoothSignedPair
      (quantitativeCanonicalTaper t)
      t (quantitativeSampleRadius t)
      (canonicalProjectiveCompletedRadius t) := by
  rw [clusterHeightDefect_eq_threeProjectiveChannels
      (quantitativeCanonicalTaper_contDiff ht)
      (quantitativeCanonicalTaper_compact ht)
      quantitativeCanonicalTaper_even
      (quantitativeCanonicalTaper_short_high ht)
      t (quantitativeSampleRadius t)]
  change
    projectiveCompletedExternalResidual
        (quantitativeCanonicalTaper t)
        t (quantitativeSampleRadius t)
      = _
  exact
    canonical_projectiveCompletedExternalResidual_eq_normalizedTsum_add_completedSmooth ht

end Synthesis
