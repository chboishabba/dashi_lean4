import Mathlib
import Mathlib.Probability.Kernel.CondDistrib
import YangMills.SequentialProjectiveKernelMeasure

/-!
# Canonical conditional-kernel extension of consistent real prefix laws

For real finite-dimensional prefix laws, the Ionescu--Tulcea producer does not
need independently supplied transition kernels.  The `(n+1)`-prefix law has a
regular conditional distribution of its last coordinate given its first `n+1`
coordinates.  Projective consistency identifies the conditioning marginal with
the selected `n`-prefix law, and `compProd_map_condDistrib` gives the exact
one-step factorization required by `RealSequentialKernelExtensionProducer`.

Thus the generic D3 extension problem for a consistent sequence of real prefix
probability laws is discharged by existing mathlib regular-conditionals plus
Ionescu--Tulcea; no cylinder-content sigma-subadditivity hypothesis is needed.
-/

open Set MeasureTheory Preorder ProbabilityTheory

namespace RequestProject.YangMills

namespace RealSequentialProjectiveFamily

/-- Initial one-coordinate law obtained from the selected zero-prefix law. -/
noncomputable def conditionalInitialMeasure
    (sequence : RealSequentialProjectiveFamily) : Measure ℝ :=
  ((sequence.marginal 0 : ProbabilityMeasure ((i : Set.Iic 0) → ℝ)) :
      Measure ((i : Set.Iic 0) → ℝ)).map
    (MeasurableEquiv.piUnique ((fun _ : Set.Iic 0 => ℝ)))

instance conditionalInitialProbability
    (sequence : RealSequentialProjectiveFamily) :
    IsProbabilityMeasure sequence.conditionalInitialMeasure := by
  unfold conditionalInitialMeasure
  exact Measure.isProbabilityMeasure_map
    (MeasurableEquiv.piUnique ((fun _ : Set.Iic 0 => ℝ))).measurable.aemeasurable

/-- The last coordinate of an `(n+1)`-prefix. -/
def realSequentialLastCoordinate
    (n : ℕ) : ((i : Set.Iic (n + 1)) → ℝ) → ℝ :=
  fun x => x ⟨n + 1, Set.mem_Iic.2 le_rfl⟩

/-- Canonical regular conditional law of the next real coordinate. -/
noncomputable def conditionalStepKernel
    (sequence : RealSequentialProjectiveFamily)
    (n : ℕ) : Kernel ((i : Set.Iic n) → ℝ) ℝ :=
  condDistrib
    (realSequentialLastCoordinate n)
    (frestrictLe₂ n.le_succ)
    (sequence.marginal (n + 1) : Measure ((i : Set.Iic (n + 1)) → ℝ))

instance conditionalStepKernelMarkov
    (sequence : RealSequentialProjectiveFamily)
    (n : ℕ) : IsMarkovKernel (sequence.conditionalStepKernel n) := by
  unfold conditionalStepKernel
  infer_instance

/-- The zero-prefix factorization required by the Ionescu--Tulcea compiler. -/
theorem conditional_initial_factorization
    (sequence : RealSequentialProjectiveFamily) :
    sequence.conditionalInitialMeasure.map
        (MeasurableEquiv.piUnique ((fun _ : Set.Iic 0 => ℝ))).symm =
      (sequence.marginal 0 : Measure ((i : Set.Iic 0) → ℝ)) := by
  unfold conditionalInitialMeasure
  rw [Measure.map_map]
  · convert Measure.map_id
      (sequence.marginal 0 : Measure ((i : Set.Iic 0) → ℝ)) using 1
    ext x i
    simp
  all_goals fun_prop

/-- Reassembling prefix plus last coordinate is literally the original prefix. -/
theorem real_sequential_step_join_prefix_last
    (n : ℕ) :
    realSequentialStepJoin n ∘
        (fun x : ((i : Set.Iic (n + 1)) → ℝ) =>
          (frestrictLe₂ n.le_succ x, realSequentialLastCoordinate n x)) =
      id := by
  funext x
  ext i
  simp [realSequentialStepJoin, realSequentialLastCoordinate,
    IicProdIoc, MeasurableEquiv.piSingleton, frestrictLe₂]

/--
Projective consistency plus the canonical regular conditional distribution gives
exactly the one-step selected-prefix factorization.
-/
theorem conditional_step_factorization
    (sequence : RealSequentialProjectiveFamily)
    (n : ℕ) :
    (((sequence.marginal n : Measure ((i : Set.Iic n) → ℝ)) ⊗ₘ
        sequence.conditionalStepKernel n).map
      (realSequentialStepJoin n)) =
    (sequence.marginal (n + 1) : Measure ((i : Set.Iic (n + 1)) → ℝ)) := by
  let μ : Measure ((i : Set.Iic (n + 1)) → ℝ) :=
    sequence.marginal (n + 1)
  have hcond :=
    compProd_map_condDistrib
      (μ := μ)
      (X := frestrictLe₂ n.le_succ)
      (Y := realSequentialLastCoordinate n)
      (by fun_prop) (by fun_prop)
  have hprefix :
      μ.map (frestrictLe₂ n.le_succ) =
        (sequence.marginal n : Measure ((i : Set.Iic n) → ℝ)) := by
    simpa [μ] using sequence.consistent n (n + 1) n.le_succ
  rw [hprefix] at hcond
  have hmapped := congrArg
    (fun ν : Measure (((i : Set.Iic n) → ℝ) × ℝ) =>
      ν.map (realSequentialStepJoin n)) hcond
  rw [Measure.map_map (by fun_prop) (real_sequential_step_join_measurable n)] at hmapped
  rw [real_sequential_step_join_prefix_last n, Measure.map_id] at hmapped
  simpa [conditionalStepKernel, μ] using hmapped

/-- Canonical kernel producer: consistency alone supplies the D3 extension data. -/
noncomputable def toConditionalKernelExtensionProducer
    (sequence : RealSequentialProjectiveFamily) :
    RealSequentialKernelExtensionProducer where
  sequence := sequence
  initial := sequence.conditionalInitialMeasure
  initialProbability := inferInstance
  kernel := sequence.conditionalStepKernel
  kernelMarkov := fun n => inferInstance
  baseFactorization := sequence.conditional_initial_factorization
  stepFactorization := sequence.conditional_step_factorization

/-- The actual countable continuum law constructed from the consistent prefixes. -/
noncomputable def conditionalGlobalMeasure
    (sequence : RealSequentialProjectiveFamily) : Measure (ℕ → ℝ) :=
  sequence.toConditionalKernelExtensionProducer.globalMeasure

instance conditionalGlobalMeasureProbability
    (sequence : RealSequentialProjectiveFamily) :
    IsProbabilityMeasure sequence.conditionalGlobalMeasure := by
  unfold conditionalGlobalMeasure
  infer_instance

/-- Every selected finite prefix is recovered exactly. -/
theorem conditionalGlobalMeasure_prefix
    (sequence : RealSequentialProjectiveFamily)
    (n : ℕ) :
    sequence.conditionalGlobalMeasure.map (frestrictLe n) =
      (sequence.marginal n : Measure ((i : Set.Iic n) → ℝ)) :=
  sequence.toConditionalKernelExtensionProducer.globalMeasure_prefix n

/-- The canonical conditional-kernel extension is unique from its prefixes. -/
theorem conditionalGlobalMeasure_unique
    (sequence : RealSequentialProjectiveFamily)
    (ν : Measure (ℕ → ℝ))
    (hν :
      ∀ n : ℕ,
        ν.map (frestrictLe n) =
          (sequence.marginal n : Measure ((i : Set.Iic n) → ℝ))) :
    ν = sequence.conditionalGlobalMeasure :=
  sequence.toConditionalKernelExtensionProducer.globalMeasure_unique ν hν

end RealSequentialProjectiveFamily

end RequestProject.YangMills
