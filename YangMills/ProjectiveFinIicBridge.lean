import Mathlib
import YangMills.ProjectiveMarginalDiagonalTightness
import YangMills.SequentialProjectiveConditionalKernel

/-!
# Canonical bridge from `Fin (n+1)` marginals to `Iic n` prefix laws

The simultaneous compactness lane stores the `m`-coordinate law on
`Fin m → ℝ`.  Mathlib's Ionescu--Tulcea lane uses prefix laws on
`Set.Iic n → ℝ`.  These are the same finite coordinate spaces after the
canonical shift `m = n + 1`.

This file closes that bookkeeping seam.  No new tightness, consistency, or
extension assumption is introduced.
-/

open Filter Set MeasureTheory Preorder

namespace RequestProject.YangMills

/-- Canonical index equivalence `Fin (n+1) ≃ Iic n`. -/
def finSuccEquivIic (n : ℕ) : Fin (n + 1) ≃ Set.Iic n where
  toFun i := ⟨i.1, Nat.le_of_lt_succ i.2⟩
  invFun i := ⟨i.1, Nat.lt_succ_of_le i.2⟩
  left_inv i := by ext; rfl
  right_inv i := by ext; rfl

/-- Reindex a finite vector as an `Iic` prefix. -/
def realFinSuccToIic
    (n : ℕ) : (Fin (n + 1) → ℝ) → ((i : Set.Iic n) → ℝ) :=
  fun x i => x ((finSuccEquivIic n).symm i)

/-- Reindex an `Iic` prefix as a finite vector. -/
def realIicToFinSucc
    (n : ℕ) : (((i : Set.Iic n) → ℝ)) → (Fin (n + 1) → ℝ) :=
  fun x i => x (finSuccEquivIic n i)

@[simp] theorem real_iic_to_fin_succ_to_iic
    (n : ℕ) (x : Fin (n + 1) → ℝ) :
    realIicToFinSucc n (realFinSuccToIic n x) = x := by
  funext i
  simp [realIicToFinSucc, realFinSuccToIic, finSuccEquivIic]

@[simp] theorem real_fin_succ_to_iic_to_fin
    (n : ℕ) (x : (i : Set.Iic n) → ℝ) :
    realFinSuccToIic n (realIicToFinSucc n x) = x := by
  funext i
  simp [realIicToFinSucc, realFinSuccToIic, finSuccEquivIic]

/-- The reindexing map is continuous. -/
theorem real_fin_succ_to_iic_continuous
    (n : ℕ) : Continuous (realFinSuccToIic n) := by
  fun_prop

/-- The inverse reindexing map is continuous. -/
theorem real_iic_to_fin_succ_continuous
    (n : ℕ) : Continuous (realIicToFinSucc n) := by
  fun_prop

/-- Push a probability law from `Fin (n+1)` to the native sequential prefix type. -/
noncomputable def realFinSuccLawToIic
    (n : ℕ)
    (μ : ProbabilityMeasure (Fin (n + 1) → ℝ)) :
    ProbabilityMeasure ((i : Set.Iic n) → ℝ) :=
  μ.map (real_fin_succ_to_iic_continuous n).measurable.aemeasurable

/-- Reindexing commutes literally with taking a shorter prefix. -/
theorem real_fin_iic_prefix_commutes
    (a b : ℕ) (hab : a ≤ b) :
    frestrictLe₂ hab ∘ realFinSuccToIic b =
      realFinSuccToIic a ∘
        realFinPrefixProjection (a + 1) (b + 1) (Nat.succ_le_succ hab) := by
  funext x i
  rfl

namespace RealSimultaneousMarginalSubsequence

/--
The simultaneous finite-dimensional limit family, reindexed into mathlib's
sequential `Iic` prefix convention.
-/
noncomputable def toSequentialProjectiveFamily
    {Ω : Type*} [MeasurableSpace Ω]
    {family : RealCanonicalProjectiveMarginalFamily Ω}
    (diag : RealSimultaneousMarginalSubsequence family) :
    RealSequentialProjectiveFamily where
  marginal := fun n => realFinSuccLawToIic n (diag.limit (n + 1))
  consistent := by
    intro a b hab
    unfold realFinSuccLawToIic
    rw [Measure.map_map]
    · rw [real_fin_iic_prefix_commutes a b hab]
      rw [Measure.map_map]
      · have hcons := diag.limit_consistent
          (a + 1) (b + 1) (Nat.succ_le_succ hab)
        change
          (diag.limit (b + 1)).map
              (real_fin_prefix_projection_measurable
                (a + 1) (b + 1) (Nat.succ_le_succ hab)).aemeasurable =
            diag.limit (a + 1) at hcons
        rw [hcons]
      all_goals fun_prop
    all_goals fun_prop

/-- The sequential prefix law is exactly the reindexed simultaneous limit. -/
theorem toSequentialProjectiveFamily_marginal
    {Ω : Type*} [MeasurableSpace Ω]
    {family : RealCanonicalProjectiveMarginalFamily Ω}
    (diag : RealSimultaneousMarginalSubsequence family)
    (n : ℕ) :
    diag.toSequentialProjectiveFamily.marginal n =
      realFinSuccLawToIic n (diag.limit (n + 1)) := rfl

/--
The canonical conditional-kernel extension of the simultaneous limits.
This closes the generic D3 chain from tight finite marginals to one countable law.
-/
noncomputable def conditionalGlobalMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    {family : RealCanonicalProjectiveMarginalFamily Ω}
    (diag : RealSimultaneousMarginalSubsequence family) :
    Measure (ℕ → ℝ) :=
  diag.toSequentialProjectiveFamily.conditionalGlobalMeasure

instance conditionalGlobalMeasureProbability
    {Ω : Type*} [MeasurableSpace Ω]
    {family : RealCanonicalProjectiveMarginalFamily Ω}
    (diag : RealSimultaneousMarginalSubsequence family) :
    IsProbabilityMeasure diag.conditionalGlobalMeasure := by
  unfold conditionalGlobalMeasure
  infer_instance

/-- Every nonempty finite marginal is recovered exactly, modulo the canonical reindexing. -/
theorem conditionalGlobalMeasure_prefix
    {Ω : Type*} [MeasurableSpace Ω]
    {family : RealCanonicalProjectiveMarginalFamily Ω}
    (diag : RealSimultaneousMarginalSubsequence family)
    (n : ℕ) :
    diag.conditionalGlobalMeasure.map (frestrictLe n) =
      (realFinSuccLawToIic n (diag.limit (n + 1)) :
        Measure ((i : Set.Iic n) → ℝ)) := by
  exact diag.toSequentialProjectiveFamily.conditionalGlobalMeasure_prefix n

end RealSimultaneousMarginalSubsequence

end RequestProject.YangMills
