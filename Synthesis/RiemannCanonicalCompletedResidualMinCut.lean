import Synthesis.RiemannProjectiveCompletedResidualCircularityFirewall
import Synthesis.RiemannReflectionDoubledProjectiveGate
import Synthesis.RiemannNormalizedProjectiveHorizontalSameOrdSign

/-!
# The completed off-ordinate residual under an off-line target

The completed residual

  R_completed(t)
    = (1/(2t)) sum'_{off} A_rho^proj
      + 2 <k_proj, -(mu+Pi_X)>

is exactly the literal cluster height defect.

Therefore, under the hypothesis that an actual zero rho at ordinate t is
off-line, the already-proved reflection-pair positivity gives

  0 < 2 D_rho <= R_completed(t).

This is an important non-circularity firewall.  A theorem asserting
R_completed <= 0, or more generally R_completed < 2 D_rho, is not an
accounting consequence of the explicit formula: it is already a prize-facing
high-side contradiction theorem.
-/

noncomputable section

open Complex
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilSameOrdinateEvenCone
open Zeta23Bridge.LiteralWeilClusterTwoRadiusProfile
open Zeta23Bridge.LiteralWeilTwoRadiusSeparationGate

/-- Named canonical completed off-ordinate residual. -/
def canonicalOffCompletedResidual (t : ℝ) : ℝ :=
  (1 / (2 * t)) *
    (∑' rho : ((SameOrd t)ᶜ : Set Zeros),
      normalizedProjectiveOffZeroAtom t (rho : Zeros))
    +
  2 * projectiveRvMCompletedSmoothSignedPair
    (quantitativeCanonicalTaper t)
    t (quantitativeSampleRadius t)
    (canonicalProjectiveCompletedRadius t)

/-- The named completed residual is exactly the literal cluster. -/
theorem canonicalOffCompletedResidual_eq_cluster
    {t : ℝ} (ht : 18 ≤ t) :
    canonicalOffCompletedResidual t
      =
    clusterHeightDefect
      (quantitativeCanonicalTaper t)
      t (quantitativeSampleRadius t) := by
  unfold canonicalOffCompletedResidual
  exact canonical_offCompletedResidual_eq_clusterHeightDefect ht

/-- An actual high off-line zero forces the completed residual to dominate the
doubled target defect. -/
theorem two_targetDefect_le_canonicalOffCompletedResidual
    {t : ℝ} (ht : 18 ≤ t)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    2 *
      zeroHeightDefect
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t)
        rho
      ≤
    canonicalOffCompletedResidual t := by
  rw [canonicalOffCompletedResidual_eq_cluster ht]
  exact gateData_two_targetDefect_le_cluster
    (quantitativeCanonicalGateData ht) him hoff

/-- The same residual is strictly positive under an off-line target. -/
theorem canonicalOffCompletedResidual_pos_of_offLine
    {t : ℝ} (ht : 18 ≤ t)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0) :
    0 < canonicalOffCompletedResidual t := by
  have hD := canonical_zeroHeightDefect_pos ht hoff
  have hlo :=
    two_targetDefect_le_canonicalOffCompletedResidual ht him hoff
  linarith

/-- A nonpositive signed theorem for the completed residual would already rule
out every high off-line zero. -/
theorem false_of_canonicalOffCompletedResidual_nonpos
    {t : ℝ} (ht : 18 ≤ t)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0)
    (hres : canonicalOffCompletedResidual t ≤ 0) :
    False := by
  have hpos :=
    canonicalOffCompletedResidual_pos_of_offLine ht him hoff
  linarith

/-- Likewise, the exact strict cut is itself the remaining prize-facing
high-side producer. -/
theorem false_of_canonicalOffCompletedResidual_lt_two_target
    {t : ℝ} (ht : 18 ≤ t)
    {rho : Zeros}
    (him : (rho : ℂ).im = t)
    (hoff : heightOf rho ≠ 0)
    (hstrict :
      canonicalOffCompletedResidual t
        <
      2 *
        zeroHeightDefect
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t)
          rho) :
    False := by
  have hlo :=
    two_targetDefect_le_canonicalOffCompletedResidual ht him hoff
  linarith

end Synthesis
