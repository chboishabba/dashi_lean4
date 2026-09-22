import Mathlib

/-!
# Canonical periodic Navier--Stokes completion leaves

This file installs the ordinary real-analysis theorem used by the DASHI
R393 temporal boundary.  It deliberately does not claim the genuinely new
R423 cutoff-uniform signed-companion estimate.

The Simon/Aubin--Lions and weak-* leaves are kept as named source interfaces
below so downstream code can depend on the exact statements without confusing
an imported/source theorem with the open R423 Navier--Stokes estimate.
-/

open MeasureTheory
open Set

namespace DASHI.NavierStokes.CanonicalLeaves

/-- The exact ordinary FTC used by the R393 temporal observable. -/
theorem offDiagonalFundamentalTheorem
    (F : ℝ → ℝ) (a b : ℝ)
    (hF : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ F x)
    (hInt : IntervalIntegrable (deriv F) volume a b) :
    (∫ x in a..b, deriv F x) = F b - F a :=
  intervalIntegral.integral_deriv_eq_sub hF hInt

/--
A source-level interface for the selected Simon/Aubin--Lions instantiation.
The fields are intentionally the hypotheses and the exact strong-convergence
conclusion consumed by DASHI; no Navier--Stokes-specific estimate is hidden
inside this record.
-/
structure CriticalSimonSourceInstance
    (Galerkin LimitState HThreeHalf HOneHalf HMinusHalf : Type*) : Prop where
  uniformlyBoundedL2HThreeHalf : Prop
  uniformlyBoundedTimeDerivativeLFourThirdHMinusHalf : Prop
  compactEmbeddingHThreeHalfToHOneHalf : Prop
  continuousEmbeddingHOneHalfToHMinusHalf : Prop
  strongL2HOneHalfSubsequence : Prop
  sourceImplication :
    uniformlyBoundedL2HThreeHalf →
    uniformlyBoundedTimeDerivativeLFourThirdHMinusHalf →
    compactEmbeddingHThreeHalfToHOneHalf →
    continuousEmbeddingHOneHalfToHMinusHalf →
    strongL2HOneHalfSubsequence

/--
Source-level interface for the weak-* lower-semicontinuity step used after
extracting the critical L∞_t H^(1/2)_x subsequence.
-/
structure CriticalWeakStarLiminfSourceInstance
    (Sequence LimitState : Type*) : Prop where
  weakStarConverges : Prop
  uniformCriticalBound : Prop
  weakStarCriticalLowerSemicontinuity : Prop
  sourceImplication :
    weakStarConverges →
    uniformCriticalBound →
    weakStarCriticalLowerSemicontinuity

/--
The canonical frontier remains separated: ordinary analysis may be installed
without manufacturing the open cutoff-uniform signed-companion payment.
-/
def R423CutoffUniformSignedCompanionBudgetIsSeparate : Prop := True

theorem r423_cutoff_uniform_signed_companion_budget_is_separate :
    R423CutoffUniformSignedCompanionBudgetIsSeparate := by
  trivial

end DASHI.NavierStokes.CanonicalLeaves
