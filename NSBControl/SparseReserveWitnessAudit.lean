import Mathlib.Tactic

/-!
# R823 exact sparse Fourier snapshot: signed-rate falsification gate

The independently evaluated six-mode, reality-conjugate sparse Fourier
snapshot has three complex seed modes (1,0,0), (0,1,0), (1,1,0).
The independent Python evaluator supplies the coefficients below.

This module verifies the *real algebraic sign* of the resulting
irrational-valued polynomial. It is NOT a formal bridge from that Python
evaluator to the R408 system or an existence theorem for its trajectory.

The missing physical promotion remains:
  (a) selected rational/real helical carrier and projection normalization;
  (b) same-object identification with R815 on the live Galerkin state;
  (c) local finite-dimensional flow and a genuine time-integral theorem.
-/

namespace NSBControl.SparseReserveWitnessAudit

noncomputable def commutatorWork : ℝ := -284 - 59 * Real.sqrt 2

def criticalProduction : ℝ := 0
def criticalDissipation : ℝ := 108

noncomputable def completeInstantaneousRate : ℝ :=
  6 * (12 * commutatorWork - criticalProduction + criticalDissipation)

theorem exactSnapshotRate :
    completeInstantaneousRate = -19800 - 4248 * Real.sqrt 2 := by
  unfold completeInstantaneousRate commutatorWork
    criticalProduction criticalDissipation
  ring

theorem exactSnapshotRateStrictlyNegative :
    completeInstantaneousRate < 0 := by
  rw [exactSnapshotRate]
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

/-- The amplitude homogeneity of THIS evaluated finite Fourier polynomial:
    (mixed u × nonlinear-forcing slot) is quintic, while viscosity is quadratic.
    The weighted production happens to vanish for this radius-one snapshot. -/
noncomputable def amplitudeRate (a : ℝ) : ℝ :=
  6 * (12 * commutatorWork * a ^ 5
       - criticalProduction * a ^ 3
       + criticalDissipation * a ^ 2)

theorem amplitudeAtOneMatchesSnapshot :
    amplitudeRate 1 = completeInstantaneousRate := by
  unfold amplitudeRate completeInstantaneousRate
  ring

theorem amplitudeSignReversalPositive :
    0 < amplitudeRate (-1) := by
  dsimp [amplitudeRate, commutatorWork,
    criticalProduction, criticalDissipation]
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

theorem amplitudeHalfNegative :
    amplitudeRate (1 / 2) < 0 := by
  dsimp [amplitudeRate, commutatorWork,
    criticalProduction, criticalDissipation]
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

/-- If the actual live R408/R815 signed rate at time zero is independently
    proved to equal this snapshot, a universal *pointwise* nonnegative-rate
    theorem is false. This does not by itself falsify the integrated W2
    inequality, nor a genuine NS existence theorem. -/
theorem negativeSnapshotRulesOutPointwiseNonnegativity
    (liveRate : ℝ → ℝ)
    (samePhysicalRateAtZero : liveRate 0 = completeInstantaneousRate) :
    ¬ (∀ t, 0 ≤ liveRate t) := by
  intro h
  have hzero := h 0
  rw [samePhysicalRateAtZero] at hzero
  exact (not_le.mpr exactSnapshotRateStrictlyNegative) hzero

end NSBControl.SparseReserveWitnessAudit
