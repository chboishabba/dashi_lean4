import Mathlib

/-!
# Canonical periodic Navier--Stokes completion leaves

This file installs the ordinary real-analysis statements that can be discharged
directly from mathlib around the current DASHI periodic-NS frontier.

It deliberately does not claim the genuinely new cutoff-uniform direct
signed-companion estimate (Agda R503/R592, equivalently feeding the older R423
consumer). The source theorem for Simon/Aubin--Lions is also kept explicit.
-/

open Filter MeasureTheory Set Topology

namespace DASHI.NavierStokes.CanonicalLeaves

/-! ## P2: scalar FTC -/

/-- The exact ordinary FTC used by the R393/R564 temporal observable. -/
theorem offDiagonalFundamentalTheorem
    (F : ℝ → ℝ) (a b : ℝ)
    (hF : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ F x)
    (hInt : IntervalIntegrable (deriv F) volume a b) :
    (∫ x in a..b, deriv F x) = F b - F a :=
  intervalIntegral.integral_deriv_eq_sub hF hInt

/-! ## P3: finite-time exponent downgrade and time-derivative assembly -/

/-- On a finite measure space, every L2 function is in L^(4/3). -/
theorem memLp_fourThird_of_memLp_two
    {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] [NormedAddCommGroup E]
    {f : α → E}
    (hf : MemLp f (ENNReal.ofReal 2) μ) :
    MemLp f (ENNReal.ofReal (4 / 3 : ℝ)) μ := by
  exact hf.mono_exponent (ENNReal.ofReal_le_ofReal (by norm_num))

/-- Exact decomposition surface for the Galerkin time derivative in H^(-1/2). -/
structure CriticalTimeDerivativeDecomposition
    (α HMinusHalf : Type*) [MeasurableSpace α]
    [NormedAddCommGroup HMinusHalf] (μ : Measure α) where
  viscousPart : α → HMinusHalf
  nonlinearPart : α → HMinusHalf
  timeDerivative : α → HMinusHalf
  timeDerivative_eq : timeDerivative = viscousPart + nonlinearPart
  viscousL2 : MemLp viscousPart (ENNReal.ofReal 2) μ
  nonlinearLFourThird :
    MemLp nonlinearPart (ENNReal.ofReal (4 / 3 : ℝ)) μ

/-- Final P3 assembly on a finite time interval. -/
theorem critical_timeDerivative_memLp_fourThird
    {α HMinusHalf : Type*} [MeasurableSpace α]
    [NormedAddCommGroup HMinusHalf] {μ : Measure α}
    [IsFiniteMeasure μ]
    (D : CriticalTimeDerivativeDecomposition α HMinusHalf μ) :
    MemLp D.timeDerivative (ENNReal.ofReal (4 / 3 : ℝ)) μ := by
  rw [D.timeDerivative_eq]
  exact (memLp_fourThird_of_memLp_two D.viscousL2).add
    D.nonlinearLFourThird

/-!
The remaining spatial estimate feeding nonlinearLFourThird is the standard
Sobolev/Holder chain from the critical barrier. It remains carrier-specific
and is not replaced here by an unrelated abstract norm inequality.
-/

/-! ## P4: exact Simon source contract -/

/--
The selected Simon/Aubin--Lions source theorem contract. This records the
published theorem boundary; it does not assert that the concrete DASHI
Sobolev carriers have already instantiated it.
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

/-! ## P5: weak-* compactness and norm lower semicontinuity -/

/-- Sequential Banach--Alaoglu for a closed dual ball, directly from mathlib. -/
theorem weakStar_closedBall_seqCompact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace.SeparableSpace E]
    (r : ℝ) :
    IsSeqCompact
      (WeakDual.toStrongDual ⁻¹'
        Metric.closedBall (0 : StrongDual ℝ E) r) := by
  simpa using
    (WeakDual.isSeqCompact_closedBall ℝ E
      (0 : StrongDual ℝ E) r)

/-- The dual norm is lower semicontinuous for the weak-* topology. -/
theorem weakStar_dualNorm_lowerSemicontinuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    LowerSemicontinuous
      (fun f : WeakDual ℝ E => ‖WeakDual.toStrongDual f‖) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro r
  have hset :
      (fun f : WeakDual ℝ E => ‖WeakDual.toStrongDual f‖) ⁻¹' Set.Iic r =
        WeakDual.toStrongDual ⁻¹'
          Metric.closedBall (0 : StrongDual ℝ E) r := by
    ext f
    simp [Metric.mem_closedBall, dist_eq_norm]
  rw [hset]
  exact WeakDual.isClosed_closedBall (𝕜 := ℝ) (E := E)
    (0 : StrongDual ℝ E) r

/-- Eventual lower-bound form of weak-* norm lower semicontinuity. -/
theorem weakStar_norm_eventually_gt_of_lt_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℕ → WeakDual ℝ E} {u∞ : WeakDual ℝ E}
    (hu : Tendsto u atTop (𝓝 u∞))
    {c : ℝ} (hc : c < ‖WeakDual.toStrongDual u∞‖) :
    ∀ᶠ n in atTop, c < ‖WeakDual.toStrongDual (u n)‖ := by
  exact hu.eventually
    ((weakStar_dualNorm_lowerSemicontinuous (E := E)) u∞ c hc)

/-- Adapter for identifying the concrete critical Linfinity carrier with a weak-* dual. -/
structure CriticalWeakStarLiminfSourceInstance
    (Sequence LimitState : Type*) : Prop where
  weakStarConverges : Prop
  uniformCriticalBound : Prop
  weakStarCriticalLowerSemicontinuity : Prop
  sourceImplication :
    weakStarConverges →
    uniformCriticalBound →
    weakStarCriticalLowerSemicontinuity

/-! ## Hard mathematical boundary -/

def R503CutoffUniformDirectOffDiagonalBudgetIsSeparate : Prop := True

theorem r503_cutoff_uniform_direct_offDiagonal_budget_is_separate :
    R503CutoffUniformDirectOffDiagonalBudgetIsSeparate := by
  trivial

/-- Backwards-compatible name for the older R423-facing cut. -/
def R423CutoffUniformSignedCompanionBudgetIsSeparate : Prop :=
  R503CutoffUniformDirectOffDiagonalBudgetIsSeparate

theorem r423_cutoff_uniform_signed_companion_budget_is_separate :
    R423CutoffUniformSignedCompanionBudgetIsSeparate := by
  trivial

end DASHI.NavierStokes.CanonicalLeaves
