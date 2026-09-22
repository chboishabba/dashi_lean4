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


/--
Hölder in time for the critical nonlinear term.  This is the exact reusable
L^4_t × L^2_t -> L^(4/3)_t step; all spatial Sobolev information is carried by
the continuous bilinear map B.
-/
theorem memLp_bilinear_four_two_fourThird
    {α E F G : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace ℝ E] [NormedSpace ℝ F] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G)
    {f : α → E} {g : α → F}
    (hHolder :
      ENNReal.HolderTriple
        (ENNReal.ofReal 4)
        (ENNReal.ofReal 2)
        (ENNReal.ofReal (4 / 3 : ℝ)))
    (hf : MemLp f (ENNReal.ofReal 4) μ)
    (hg : MemLp g (ENNReal.ofReal 2) μ) :
    MemLp (fun t => B (f t) (g t))
      (ENNReal.ofReal (4 / 3 : ℝ)) μ := by
  letI := hHolder
  exact B.memLp_of_bilin (ENNReal.ofReal (4 / 3 : ℝ)) hf hg

/-- Continuous spatial embeddings preserve the time Lp membership. -/
theorem memLp_comp_continuousLinearMap
    {α E F : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace ℝ F]
    {p : ENNReal} (L : E →L[ℝ] F) {f : α → E}
    (hf : MemLp f p μ) :
    MemLp (fun t => L (f t)) p μ := by
  simpa [Function.comp_def] using L.comp_memLp' hf

/--
B1+B2 compiler on typed spatial carriers.

The viscous map represents H^(3/2) -> H^(-1/2), while nonlinearMap represents
the spatial Sobolev/Hölder product H^1 × H^(1/2) -> H^(-1/2).  Thus the only
remaining carrier-specific work is to instantiate these continuous maps and
the L^4_t H^1 / L^2_t H^(1/2) bounds.
-/
theorem critical_timeDerivative_of_linear_bilinear
    {α HThreeHalf HOne HGradientHalf HMinusHalf : Type*}
    [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    [NormedAddCommGroup HThreeHalf] [NormedAddCommGroup HOne]
    [NormedAddCommGroup HGradientHalf] [NormedAddCommGroup HMinusHalf]
    [NormedSpace ℝ HThreeHalf] [NormedSpace ℝ HOne]
    [NormedSpace ℝ HGradientHalf] [NormedSpace ℝ HMinusHalf]
    (viscousMap : HThreeHalf →L[ℝ] HMinusHalf)
    (nonlinearMap : HOne →L[ℝ] HGradientHalf →L[ℝ] HMinusHalf)
    (uThreeHalf : α → HThreeHalf)
    (uOne : α → HOne)
    (gradHalf : α → HGradientHalf)
    (timeDerivative : α → HMinusHalf)
    (hHolder :
      ENNReal.HolderTriple
        (ENNReal.ofReal 4)
        (ENNReal.ofReal 2)
        (ENNReal.ofReal (4 / 3 : ℝ)))
    (huThreeHalf : MemLp uThreeHalf (ENNReal.ofReal 2) μ)
    (huOne : MemLp uOne (ENNReal.ofReal 4) μ)
    (hgradHalf : MemLp gradHalf (ENNReal.ofReal 2) μ)
    (hEquation :
      timeDerivative =
        (fun t =>
          viscousMap (uThreeHalf t) +
            nonlinearMap (uOne t) (gradHalf t))) :
    MemLp timeDerivative (ENNReal.ofReal (4 / 3 : ℝ)) μ := by
  have hviscous2 :
      MemLp (fun t => viscousMap (uThreeHalf t))
        (ENNReal.ofReal 2) μ :=
    memLp_comp_continuousLinearMap viscousMap huThreeHalf
  have hviscous :
      MemLp (fun t => viscousMap (uThreeHalf t))
        (ENNReal.ofReal (4 / 3 : ℝ)) μ :=
    memLp_fourThird_of_memLp_two hviscous2
  have hnonlinear :
      MemLp (fun t => nonlinearMap (uOne t) (gradHalf t))
        (ENNReal.ofReal (4 / 3 : ℝ)) μ :=
    memLp_bilinear_four_two_fourThird
      nonlinearMap hHolder huOne hgradHalf
  rw [hEquation]
  exact hviscous.add hnonlinear

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
The selected Simon/Aubin--Lions source theorem contract. Every hypothesis and
conclusion is indexed by the concrete Galerkin sequence, limit object, and
selected Sobolev carriers. This records the published theorem boundary without
asserting that DASHI's concrete carriers have already instantiated it.
-/
structure CriticalSimonSourceInstance
    (Galerkin LimitState HThreeHalf HOneHalf HMinusHalf : Type*)
    (galerkins : ℕ → Galerkin)
    (limit : LimitState)
    (UniformL2In :
      (ℕ → Galerkin) → Type* → Prop)
    (UniformTimeDerivativeLFourThirdIn :
      (ℕ → Galerkin) → Type* → Prop)
    (CompactEmbedding : Type* → Type* → Prop)
    (ContinuousEmbedding : Type* → Type* → Prop)
    (StrongL2SubsequenceIn :
      (ℕ → Galerkin) → LimitState → Type* → Prop) : Prop where
  uniformlyBoundedL2HThreeHalf :
    UniformL2In galerkins HThreeHalf
  uniformlyBoundedTimeDerivativeLFourThirdHMinusHalf :
    UniformTimeDerivativeLFourThirdIn galerkins HMinusHalf
  compactEmbeddingHThreeHalfToHOneHalf :
    CompactEmbedding HThreeHalf HOneHalf
  continuousEmbeddingHOneHalfToHMinusHalf :
    ContinuousEmbedding HOneHalf HMinusHalf
  strongL2HOneHalfSubsequence :
    StrongL2SubsequenceIn galerkins limit HOneHalf
  sourceImplication :
    UniformL2In galerkins HThreeHalf →
    UniformTimeDerivativeLFourThirdIn galerkins HMinusHalf →
    CompactEmbedding HThreeHalf HOneHalf →
    ContinuousEmbedding HOneHalf HMinusHalf →
    StrongL2SubsequenceIn galerkins limit HOneHalf

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


/--
Concrete sequential Banach--Alaoglu extraction for any sequence lying in one
weak-* closed dual ball.
-/
theorem weakStar_closedBall_has_subsequence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace.SeparableSpace E]
    (r : ℝ) (u : ℕ → WeakDual ℝ E)
    (hu :
      ∀ n,
        WeakDual.toStrongDual (u n) ∈
          Metric.closedBall (0 : StrongDual ℝ E) r) :
    ∃ u∞ : WeakDual ℝ E,
      WeakDual.toStrongDual u∞ ∈
        Metric.closedBall (0 : StrongDual ℝ E) r ∧
      ∃ φ : ℕ → ℕ,
        StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 u∞) := by
  simpa only [Set.mem_preimage] using
    (weakStar_closedBall_seqCompact r hu)

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


/--
Literal liminf form used by the critical barrier.  A uniform closed-ball bound
supplies the upper coboundedness needed by liminf on ℝ; norm nonnegativity
supplies the lower boundedness.
-/
theorem weakStar_norm_le_liminf
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℕ → WeakDual ℝ E} {u∞ : WeakDual ℝ E}
    (hu : Tendsto u atTop (𝓝 u∞))
    (r : ℝ)
    (hbound : ∀ n, ‖WeakDual.toStrongDual (u n)‖ ≤ r) :
    ‖WeakDual.toStrongDual u∞‖ ≤
      Filter.liminf
        (fun n => ‖WeakDual.toStrongDual (u n)‖) atTop := by
  have hcob :
      IsCoboundedUnder (· ≥ ·) atTop
        (fun n => ‖WeakDual.toStrongDual (u n)‖) :=
    IsCoboundedUnder.of_frequently_le
      (Filter.Frequently.of_forall hbound)
  have hbdd :
      IsBoundedUnder (· ≥ ·) atTop
        (fun n => ‖WeakDual.toStrongDual (u n)‖) :=
    isBoundedUnder_of_eventually_ge
      (Filter.Eventually.of_forall fun n => norm_nonneg _)
  exact (le_liminf_iff hcob hbdd).2
    (fun c hc =>
      weakStar_norm_eventually_gt_of_lt_limit hu hc)

/-- Typed adapter for weak-* convergence and the critical liminf on one concrete sequence/limit. -/
structure CriticalWeakStarLiminfSourceInstance
    (Sequence LimitState : Type*)
    (sequence : ℕ → Sequence)
    (limit : LimitState)
    (WeakStarConverges : (ℕ → Sequence) → LimitState → Prop)
    (UniformCriticalBound : (ℕ → Sequence) → Prop)
    (CriticalNormLiminf : (ℕ → Sequence) → LimitState → Prop) : Prop where
  weakStarConverges : WeakStarConverges sequence limit
  uniformCriticalBound : UniformCriticalBound sequence
  weakStarCriticalLowerSemicontinuity : CriticalNormLiminf sequence limit
  sourceImplication :
    WeakStarConverges sequence limit →
    UniformCriticalBound sequence →
    CriticalNormLiminf sequence limit

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
