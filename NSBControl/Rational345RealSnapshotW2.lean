import Mathlib.Tactic
import NSBControl.Rational345ReserveWitness
import NSBControl.Rational345RealSnapshotHelicalRows

/-!
# W2: genuine real evolving observable specializes to R850 at the snapshot

This closes the conceptual backend square for R830.  The public selected rate
is the genuine real radius-four observable used along the local ODE.  At the
3-4-5 initial state it is shown, through the literal finite operators, to equal
exactly the R850/R829 value -28273644/125.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345RealSnapshotW2

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345RealSnapshotSparse
open Rational345RealSnapshotRows
open Rational345RealSnapshotHelicalSparse
open Rational345RealSnapshotHelicalRows

classical

------------------------------------------------------------------------
-- Eight actual coherent-work rows.
------------------------------------------------------------------------

private macro "work_row_simp" : tactic =>
  `(tactic|
    (simp [outputCommutatorWork, coherentWork, hermitianDot,
      m₁, m₂, m₃, m₄, m₅, m₆, m₇, m₈,
      g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈,
      Rational345RealSnapshotHelicalRows.c,
      Rational345RealSnapshotHelicalRows.v] <;> norm_num <;> ring))

theorem work₁_exact : outputCommutatorWork u₀ k₁ = -48 := by
  rw [outputCommutatorWork, fixedOutputMixed_k₁, fixedOutputCommutator_k₁]
  work_row_simp

theorem work₂_exact : outputCommutatorWork u₀ k₂ = (322917 : ℝ) / 250 := by
  rw [outputCommutatorWork, fixedOutputMixed_k₂, fixedOutputCommutator_k₂]
  work_row_simp

theorem work₃_exact : outputCommutatorWork u₀ k₃ = -48 := by
  rw [outputCommutatorWork, fixedOutputMixed_k₃, fixedOutputCommutator_k₃]
  work_row_simp

theorem work₄_exact : outputCommutatorWork u₀ k₄ = -(428272 : ℝ) / 125 := by
  rw [outputCommutatorWork, fixedOutputMixed_k₄, fixedOutputCommutator_k₄]
  work_row_simp

theorem work₅_exact : outputCommutatorWork u₀ k₅ = -(428272 : ℝ) / 125 := by
  rw [outputCommutatorWork, fixedOutputMixed_k₅, fixedOutputCommutator_k₅]
  work_row_simp

theorem work₆_exact : outputCommutatorWork u₀ k₆ = -48 := by
  rw [outputCommutatorWork, fixedOutputMixed_k₆, fixedOutputCommutator_k₆]
  work_row_simp

theorem work₇_exact : outputCommutatorWork u₀ k₇ = (322917 : ℝ) / 250 := by
  rw [outputCommutatorWork, fixedOutputMixed_k₇, fixedOutputCommutator_k₇]
  work_row_simp

theorem work₈_exact : outputCommutatorWork u₀ k₈ = -48 := by
  rw [outputCommutatorWork, fixedOutputMixed_k₈, fixedOutputCommutator_k₈]
  work_row_simp

lemma outputCommutatorWork_zero_of_not_mem_active
    {k : Mode} (hz : ¬ isZeroMode k) (hk : k ∉ activeOutputs) :
    outputCommutatorWork u₀ k = 0 := by
  rw [outputCommutatorWork, fixedOutputMixed_u₀_eq_sparse,
      sparseMixed_zero_of_not_mem_active hz hk]
  simp [coherentWork, hermitianDot]

lemma global_work_sum_active :
    globalCoherentWork u₀ =
      ∑ k in activeOutputs, outputCommutatorWork u₀ k := by
  unfold globalCoherentWork
  symm
  apply Finset.sum_subset (by simp)
  intro k hkUniv hkActive
  by_cases hz : isZeroMode k
  · simp [hz]
  · simp [hz, outputCommutatorWork_zero_of_not_mem_active hz hkActive]

/-- Actual real R692 coherent-work aggregate. -/
theorem globalCoherentWork_u₀_exact :
    globalCoherentWork u₀ = -(557627 : ℝ) / 125 := by
  rw [global_work_sum_active]
  simp [activeOutputs, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈,
    work₁_exact, work₂_exact, work₃_exact, work₄_exact,
    work₅_exact, work₆_exact, work₇_exact, work₈_exact]
  norm_num

------------------------------------------------------------------------
-- Six actual critical production/dissipation rows.
------------------------------------------------------------------------

lemma modalProduction_zero_of_not_mem_seed
    {k : Mode} (hk : k ∉ seedModes) : modalProduction u₀ k = 0 := by
  rw [modalProduction, u₀_zero_of_not_mem_seed hk]
  simp [hermitianDot]

lemma modalDissipation_zero_of_not_mem_seed
    {k : Mode} (hk : k ∉ seedModes) : modalDissipation u₀ k = 0 := by
  rw [modalDissipation, u₀_zero_of_not_mem_seed hk]
  simp [hermitianDot]

lemma production_sum_seed :
    criticalProduction u₀ = ∑ k in seedModes, modalProduction u₀ k := by
  unfold criticalProduction
  symm
  apply Finset.sum_subset (by simp)
  intro k hkUniv hkSeed
  by_cases hz : isZeroMode k
  · simp [hz]
  · simp [hz, modalProduction_zero_of_not_mem_seed hkSeed]

lemma dissipation_sum_seed :
    criticalDissipation u₀ = ∑ k in seedModes, modalDissipation u₀ k := by
  unfold criticalDissipation
  symm
  apply Finset.sum_subset (by simp)
  intro k hkUniv hkSeed
  by_cases hz : isZeroMode k
  · simp [hz]
  · simp [hz, modalDissipation_zero_of_not_mem_seed hkSeed]

private macro "energy_row_simp" : tactic =>
  `(tactic|
    (simp [modalProduction, modalDissipation, criticalWeight, maxAbs,
      hermitianDot, normSq, kReal, kInt, axisInt,
      u₀, v300, v040, v340, vecConj,
      k300, km300, k040, k0m40, k340, km3m40,
      k₁, k₂, k₄, k₅, k₇, k₈,
      f₁, f₂, f₄, f₅, f₇, f₈,
      Rational345RealSnapshotRows.c,
      Rational345RealSnapshotRows.v] <;> norm_num <;> ring))

theorem production₁_exact : modalProduction u₀ k₁ = -128 := by
  rw [projectedNonlinearity_k₁]
  energy_row_simp

theorem production₂_exact : modalProduction u₀ k₂ = -672 := by
  rw [projectedNonlinearity_k₂]
  energy_row_simp

theorem production₄_exact : modalProduction u₀ k₄ = 800 := by
  rw [projectedNonlinearity_k₄]
  energy_row_simp

theorem production₅_exact : modalProduction u₀ k₅ = 800 := by
  rw [projectedNonlinearity_k₅]
  energy_row_simp

theorem production₇_exact : modalProduction u₀ k₇ = -672 := by
  rw [projectedNonlinearity_k₇]
  energy_row_simp

theorem production₈_exact : modalProduction u₀ k₈ = -128 := by
  rw [projectedNonlinearity_k₈]
  energy_row_simp

theorem dissipation₁_exact : modalDissipation u₀ k₁ = 6425 := by
  energy_row_simp

theorem dissipation₂_exact : modalDissipation u₀ k₂ = 468 := by
  energy_row_simp

theorem dissipation₄_exact : modalDissipation u₀ k₄ = 1024 := by
  energy_row_simp

theorem dissipation₅_exact : modalDissipation u₀ k₅ = 1024 := by
  energy_row_simp

theorem dissipation₇_exact : modalDissipation u₀ k₇ = 468 := by
  energy_row_simp

theorem dissipation₈_exact : modalDissipation u₀ k₈ = 6425 := by
  energy_row_simp

theorem criticalProduction_u₀_exact : criticalProduction u₀ = 0 := by
  rw [production_sum_seed]
  simp [seedModes, k₁, k₂, k₄, k₅, k₇, k₈,
    production₁_exact, production₂_exact, production₄_exact,
    production₅_exact, production₇_exact, production₈_exact]
  norm_num

theorem criticalDissipation_u₀_exact : criticalDissipation u₀ = 15834 := by
  rw [dissipation_sum_seed]
  simp [seedModes, k₁, k₂, k₄, k₅, k₇, k₈,
    dissipation₁_exact, dissipation₂_exact, dissipation₄_exact,
    dissipation₅_exact, dissipation₇_exact, dissipation₈_exact]
  norm_num

------------------------------------------------------------------------
-- W2 commuting square.
------------------------------------------------------------------------

/-- The genuine real evolving R815-normalized observable specializes exactly
to the already-certified R850 initial value. -/
theorem selectedRate_u₀_exact : selectedRate u₀ = expectedInitialRate := by
  rw [selectedRate_public_definition,
      globalCoherentWork_u₀_exact,
      criticalProduction_u₀_exact,
      criticalDissipation_u₀_exact]
  norm_num [expectedInitialRate]

theorem selectedRate_u₀_negative : selectedRate u₀ < 0 := by
  rw [selectedRate_u₀_exact]
  exact expectedInitialRate_neg

/-- Explicit bridge to the earlier rational Lean mirror of the R850 arithmetic. -/
theorem selectedRate_u₀_eq_rationalWitness :
    selectedRate u₀ = (Rational345ReserveWitness.canonicalSignedRate : ℝ) := by
  rw [selectedRate_u₀_exact, Rational345ReserveWitness.canonicalSignedRate_exact]
  norm_num [expectedInitialRate]

end Rational345RealSnapshotW2
end NSBControl
