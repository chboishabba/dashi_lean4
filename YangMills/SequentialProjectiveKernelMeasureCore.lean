import Mathlib
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import YangMills.SequentialProjectiveCylinderMeasure

open Set MeasureTheory Preorder ProbabilityTheory

namespace RequestProject.YangMills

def realSequentialStepJoin
    (n : ℕ) :
    (((i : Set.Iic n) → ℝ) × ℝ) → ((i : Set.Iic (n + 1)) → ℝ) :=
  fun z =>
    IicProdIoc n (n + 1)
      (z.1, (MeasurableEquiv.piSingleton n) z.2)

theorem real_sequential_step_join_measurable
    (n : ℕ) : Measurable (realSequentialStepJoin n) := by
  unfold realSequentialStepJoin
  fun_prop

structure RealSequentialKernelExtensionProducer where
  sequence : RealSequentialProjectiveFamily
  initial : Measure ℝ
  initialProbability : IsProbabilityMeasure initial
  kernel : (n : ℕ) → Kernel ((i : Set.Iic n) → ℝ) ℝ
  kernelMarkov : ∀ n, IsMarkovKernel (kernel n)
  baseFactorization :
    initial.map (MeasurableEquiv.piUnique ((fun _ : Set.Iic 0 => ℝ))).symm =
      (sequence.marginal 0 : Measure ((i : Set.Iic 0) → ℝ))
  stepFactorization :
    ∀ n : ℕ,
      (((sequence.marginal n : Measure ((i : Set.Iic n) → ℝ)) ⊗ₘ kernel n).map
        (realSequentialStepJoin n)) =
      (sequence.marginal (n + 1) : Measure ((i : Set.Iic (n + 1)) → ℝ))

namespace RealSequentialKernelExtensionProducer

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
  rw [show producer.globalMeasure = trajMeasure producer.initial producer.kernel by rfl] at hn ⊢
  rw [hn] at hmapped
  calc
    (trajMeasure producer.initial producer.kernel).map (frestrictLe (n + 1)) =
        (((producer.sequence.marginal n : Measure ((i : Set.Iic n) → ℝ)) ⊗ₘ
          producer.kernel n).map (realSequentialStepJoin n)) := hmapped.symm
    _ = (producer.sequence.marginal (n + 1) :
          Measure ((i : Set.Iic (n + 1)) → ℝ)) := producer.stepFactorization n

theorem globalMeasure_prefix
    (producer : RealSequentialKernelExtensionProducer)
    (n : ℕ) :
    producer.globalMeasure.map (frestrictLe n) =
      (producer.sequence.marginal n : Measure ((i : Set.Iic n) → ℝ)) := by
  induction n with
  | zero => exact producer.globalMeasure_prefix_zero
  | succ n ih => exact producer.globalMeasure_prefix_succ n ih

noncomputable def globalProbabilityMeasure
    (producer : RealSequentialKernelExtensionProducer) :
    ProbabilityMeasure (ℕ → ℝ) :=
  ⟨producer.globalMeasure, inferInstance⟩

theorem globalMeasure_projective
    (producer : RealSequentialKernelExtensionProducer) :
    IsProjectiveLimit producer.globalMeasure
      producer.sequence.inducedMeasureFamily := by
  rw [isProjectiveLimit_nat_iff
    producer.sequence.inducedMeasureFamily_projective]
  intro n
  rw [inducedFamily_Iic producer.sequence.measureSequence n]
  exact producer.globalMeasure_prefix n

theorem globalMeasure_unique
    (producer : RealSequentialKernelExtensionProducer)
    (ν : Measure (ℕ → ℝ))
    (hν :
      ∀ n : ℕ,
        ν.map (frestrictLe n) =
          (producer.sequence.marginal n : Measure ((i : Set.Iic n) → ℝ))) :
    ν = producer.globalMeasure := by
  have hνProj :
      IsProjectiveLimit ν producer.sequence.inducedMeasureFamily := by
    rw [isProjectiveLimit_nat_iff
      producer.sequence.inducedMeasureFamily_projective]
    intro n
    rw [inducedFamily_Iic producer.sequence.measureSequence n]
    exact hν n
  exact hνProj.unique producer.globalMeasure_projective

end RealSequentialKernelExtensionProducer

end RequestProject.YangMills
