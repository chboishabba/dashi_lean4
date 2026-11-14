import Mathlib

/-!
# Continuous fifth-moment sign audit — NOT the native RH signed-fifth gap

The continuous scalar in the 12 November 2026 attachment is
  (∫ x, x^5 H'(x) H(x)) - (∫ x, x² H(x)²)(∫ x, x³ H(x)²).

For an even real function with sufficient regularity/decay the odd cubic
moment is zero and integration by parts identifies the derivative moment
with -(5/2) times the fourth moment. These are explicit hypotheses
below: this source neither constructs their analytic witnesses nor
identifies this scalar with DASHI's different discrete
`signedFifthCorrelationGapAt` operator.

Source attribution: standard parity and integration by parts; the
finite signed gap and eventual-sign target belong to the existing
DASHI RH programme. No RH theorem follows here.
-/

noncomputable section

namespace DASHI.RiemannContinuousFifthSign

open MeasureTheory

def continuousFifthGap (H : ℝ → ℝ) : ℝ :=
  (∫ x : ℝ, x ^ 5 * deriv H x * H x) -
    (∫ x : ℝ, x ^ 2 * H x ^ 2) *
      (∫ x : ℝ, x ^ 3 * H x ^ 2)

/-- Exact analytic hypotheses for the displayed continuous functional.
    In particular, no integration-by-parts boundary term is discarded
    without being accounted for by the hypothesis. -/
structure ContinuousEvenMomentCertificate (H : ℝ → ℝ) : Prop where
  cubicOddMomentZero :
    (∫ x : ℝ, x ^ 3 * H x ^ 2) = 0
  fifthIntegrationByParts :
    (∫ x : ℝ, x ^ 5 * deriv H x * H x) =
      -(5 / 2 : ℝ) * (∫ x : ℝ, x ^ 4 * H x ^ 2)

/-- Unconditional *algebraic implication* from the exact moment identities.
    This does not assert those identities for an arbitrary H. -/
theorem continuousFifthGap_eq_negative_fourth
    {H : ℝ → ℝ} (h : ContinuousEvenMomentCertificate H) :
    continuousFifthGap H =
      -(5 / 2 : ℝ) * (∫ x : ℝ, x ^ 4 * H x ^ 2) := by
  unfold continuousFifthGap
  rw [h.cubicOddMomentZero, h.fifthIntegrationByParts]
  ring

/-- The *continuous* functional has strictly negative sign when its
    fourth moment is strictly positive. This is a negative control,
    not the native RH Route-B eventual-positive assertion. -/
theorem continuousFifthGap_strictly_negative
    {H : ℝ → ℝ} (h : ContinuousEvenMomentCertificate H)
    (hfourth : 0 < ∫ x : ℝ, x ^ 4 * H x ^ 2) :
    continuousFifthGap H < 0 := by
  rw [continuousFifthGap_eq_negative_fourth h]
  linarith

theorem continuousFifthGap_not_nonnegative
    {H : ℝ → ℝ} (h : ContinuousEvenMomentCertificate H)
    (hfourth : 0 < ∫ x : ℝ, x ^ 4 * H x ^ 2) :
    ¬ 0 ≤ continuousFifthGap H := by
  exact not_le_of_gt (continuousFifthGap_strictly_negative h hfourth)

#print axioms continuousFifthGap_eq_negative_fourth
#print axioms continuousFifthGap_strictly_negative
#print axioms continuousFifthGap_not_nonnegative

end DASHI.RiemannContinuousFifthSign
