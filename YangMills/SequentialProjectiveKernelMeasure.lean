import Mathlib
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import YangMills.SequentialProjectiveCylinderMeasure

/-!
# Ionescu--Tulcea extension of a sequential projective real family

This is the alternative D3.5 compiler to the cylinder-content
sigma-subadditivity route.  A selected sequence of prefix laws is extended by
actual one-step Markov kernels.  The only same-object obligations are:

* the initial one-coordinate law agrees with the selected prefix law at `0`;
* adjoining one kernel step to the selected `n`-prefix and gluing the new
  coordinate produces the selected `(n+1)`-prefix exactly.

Ionescu--Tulcea then supplies the countable trajectory probability measure.
The proof below shows inductively that its finite prefixes are the selected
marginals, so no cylinder sigma-additivity hypothesis remains on this route.
-/

open Set MeasureTheory Preorder ProbabilityTheory

namespace RequestProject.YangMills

/-- Glue a prefix on `Iic n` and one new real coordinate into `Iic (n+1)`. -/
def realSequentialStepJoin
    (n : ℕ) :
    (((i : Set.Iic n) → ℝ) × ℝ) → ((i : Set.Iic (n + 1)) → ℝ) :=
  fun z =>
    IicProdIoc n (n + 1)
      (z.1, (MeasurableEquiv.piSingleton n) z.2)

/-- The one-step prefix gluing map is measurable. -/
theorem real_sequential_step_join_measurable
    (n : ℕ) : Measurable (realSequentialStepJoin n) := by
  unfold realSequentialStepJoin
  fun_prop

/--
The literal one-step producer for the kernel route.

`stepFactorization` is the source-facing same-object theorem: starting from the
selected `n`-prefix law, sampling the next coordinate with `kernel n`, and
reassembling the prefix gives the selected `(n+1)`-prefix law.
-/
structure RealSequentialKernelExtensionProducer where
  sequence : RealSequentialProjectiveFamily
  initial : Measure ℝ
  initialProbability : IsProbabilityMeasure initial
  kernel : (n : ℕ) →
    ProbabilityTheory.Kernel ((i : Set.Iic n) → ℝ) ℝ
  kernelMarkov : ∀ n, ProbabilityTheory.IsMarkovKernel (kernel n)
  baseFactorization :
    initial.map (MeasurableEquiv.piUnique ((fun _ : Set.Iic 0 => ℝ))).symm =
      (sequence.marginal 0 : Measure ((i : Set.Iic 0) → ℝ))
  stepFactorization :
    ∀ n : ℕ,
      (((sequence.marginal n : Measure ((i : Set.Iic n) → ℝ)) ⊗ₘ kernel n).map
        (realSequentialStepJoin n)) =
      (sequence.marginal (n + 1) : Measure ((i : Set.Iic (n + 1)) → ℝ))

namespace RealSequentialKernelExtensionProducer

/-- The Ionescu--Tulcea trajectory measure selected by the producer. -/
noncomputable def globalMeasure
    (producer : RealSequentialKernelExtensionProducer) : Measure (ℕ → ℝ) := by
  letI : IsProbabilityMeasure producer.initial := producer.initialProbability
  letI : ∀ n, IsMarkovKernel (producer.kernel n) := producer.kernelMarkov
  exact trajMeasure producer.initial producer.kernel

instance globalMeasureIsProbability
    (producer : RealSequentialKernelExtensionProducer) :
    IsProbabilityMeasure producer.globalMeasure := by
  unfold globalMeasure
  letI : IsProbabilityMeasure producer.initial := producer.initialProbability
  letI : ∀ n, IsMarkovKernel (producer.kernel n) := producer.kernelMarkov
  infer_instance

/-- The trajectory law has the selected zero-prefix law. -/
theorem globalMeasure_prefix_zero
    (producer : RealSequentialKernelExtensionProducer) :
    producer.globalMeasure.map (frestrictLe 0) =
      (producer.sequence.marginal 0 : Measure ((i : Set.Iic 0) → ℝ)) := by
  unfold globalMeasure
  letI : IsProbabilityMeasure producer.initial := producer.initialProbability
  letI : ∀ n, IsMarkovKernel (producer.kernel n) := producer.kernelMarkov
  rw [trajMeasure, Measure.map_comp _ _ (by fun_prop),
    traj_map_frestrictLe, partialTraj_self, Kernel.id_apply]
  simpa using producer.baseFactorization

/--
One Ionescu--Tulcea step transports an already-identified prefix to the next
selected prefix using the source-facing `stepFactorization` theorem.
-/
theorem globalMeasure_prefix_succ
    (producer : RealSequentialKernelExtensionProducer)
    (n : ℕ)
    (hn :
      producer.globalMeasure.map (frestrictLe n) =
        (producer.sequence.marginal n : Measure ((i : Set.Iic n) → ℝ))) :
    producer.globalMeasure.map (frestrictLe (n + 1)) =
      (producer.sequence.marginal (n + 1) :
        Measure ((i : Set.Iic (n + 1)) → ℝ)) := by
  letI : IsProbabilityMeasure producer.initial := producer.initialProbability
  letI : ∀ k, IsMarkovKernel (producer.kernel k) := producer.kernelMarkov
  have hstep :=
    map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
      (μ₀ := producer.initial) (κ := producer.kernel) (a := n)
  have hjoin :
      realSequentialStepJoin n ∘
          (fun x : ℕ → ℝ => (frestrictLe n x, x (n + 1))) =
        frestrictLe (n + 1) := by
    funext x
    ext i
    simp [realSequentialStepJoin, IicProdIoc, MeasurableEquiv.piSingleton,
      frestrictLe]
  have hmapped := congrArg
    (fun μ : Measure (((i : Set.Iic n) → ℝ) × ℝ) =>
      μ.map (realSequentialStepJoin n)) hstep
  rw [Measure.map_map (by fun_prop) (real_sequential_step_join_measurable n),
    hjoin] at hmapped
  rw [show producer.globalMeasure = trajMeasure producer.initial producer.kernel by
      rfl] at hn ⊢
  rw [hn] at hmapped
  calc
    (trajMeasure producer.initial producer.kernel).map (frestrictLe (n + 1)) =
        (((producer.sequence.marginal n : Measure ((i : Set.Iic n) → ℝ)) ⊗ₘ
          producer.kernel n).map (realSequentialStepJoin n)) := hmapped.symm
    _ = (producer.sequence.marginal (n + 1) :
          Measure ((i : Set.Iic (n + 1)) → ℝ)) := producer.stepFactorization n

/-- Every finite prefix of the trajectory law is exactly the selected prefix law. -/
theorem globalMeasure_prefix
    (producer : RealSequentialKernelExtensionProducer)
    (n : ℕ) :
    producer.globalMeasure.map (frestrictLe n) =
      (producer.sequence.marginal n : Measure ((i : Set.Iic n) → ℝ)) := by
  induction n with
  | zero => exact producer.globalMeasure_prefix_zero
  | succ n ih => exact producer.globalMeasure_prefix_succ n ih

/-- Package the trajectory measure as an actual probability measure. -/
noncomputable def globalProbabilityMeasure
    (producer : RealSequentialKernelExtensionProducer) :
    ProbabilityMeasure (ℕ → ℝ) :=
  ⟨producer.globalMeasure, inferInstance⟩

/-- D3.6 uniqueness: complete finite-prefix data determine the trajectory law. -/
theorem globalMeasure_unique
    (producer : RealSequentialKernelExtensionProducer)
    (ν : Measure (ℕ → ℝ))
    (hν :
      ∀ n : ℕ,
        ν.map (frestrictLe n) =
          (producer.sequence.marginal n : Measure ((i : Set.Iic n) → ℝ))) :
    ν = producer.globalMeasure := by
  let cylinderProducer : RealSequentialCylinderExtensionProducer :=
    { sequence := producer.sequence
      sigmaSubadditive := by
        -- The trajectory measure already realizes the projective family, so
        -- uniqueness below can be proved directly from finite prefixes.  This
        -- field is never used; constructing it would reintroduce the route we
        -- are bypassing.
        intro f hf hU
        exact le_top }
  apply Measure.ext_of_generate_finite
    (measurableCylinders (fun _ : ℕ => ℝ))
    generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders
  · intro s hs
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).mp hs
    let N := I.sup id
    have hsub : I ⊆ Set.Iic N := I.subset_Iic_sup_id
    have hνN := hν N
    have hμN := producer.globalMeasure_prefix N
    rw [cylinder, ← Measure.map_apply (measurable_restrict I) hS,
      ← restrict₂_comp_restrict hsub, ← Measure.map_map,
      hνN, ← hμN, Measure.map_map]
    all_goals fun_prop
  · rw [measure_univ]
    infer_instance

end RealSequentialKernelExtensionProducer

end RequestProject.YangMills
