import Mathlib.Tactic
import NSBControl.Rational345RealSnapshotRows

/-!
# W2 sparse real helical folds

Prunes the literal real R224/R230-style finite sums at the 3-4-5 snapshot:

* mixed fold: six velocity seeds x six velocity seeds;
* commutator fold: eight forcing modes x six velocity seeds.

This is the exact real-backend counterpart of the Agda R836/R845 pruning.
-/

open scoped BigOperators

namespace NSBControl
namespace Rational345RealSnapshotHelicalSparse

open Rational345RealRadius4
open Rational345RealInitialState
open Rational345RealSnapshotSparse
open Rational345RealSnapshotRows

classical

lemma helicalPlus_zero (k : Mode) : helicalPlus k (0 : Vec3) = 0 := by
  funext j
  fin_cases j <;>
    simp [helicalPlus, leray, curlSymbol, cross, bilinearDot, kComplex]

lemma helicalMinus_zero (k : Mode) : helicalMinus k (0 : Vec3) = 0 := by
  funext j
  fin_cases j <;>
    simp [helicalMinus, leray, curlSymbol, cross, bilinearDot, kComplex]

lemma mixedCell_zero_left (u : State) (p q : Mode) (hp : u p = 0) :
    mixedCell u p q = 0 := by
  rw [mixedCell, hp, helicalPlus_zero]
  funext j
  fin_cases j <;> simp [cross]

lemma mixedCell_zero_right (u : State) (p q : Mode) (hq : u q = 0) :
    mixedCell u p q = 0 := by
  rw [mixedCell, hq, helicalMinus_zero]
  funext j
  fin_cases j <;> simp [cross]

lemma forcingCommutatorCell_zero_forcing
    (u forcing : State) (p q : Mode) (hp : forcing p = 0) :
    forcingCommutatorCell u forcing p q = 0 := by
  rw [forcingCommutatorCell, hp, helicalPlus_zero, helicalMinus_zero]
  funext j
  fin_cases j <;> simp [cross]

lemma forcingCommutatorCell_zero_velocity
    (u forcing : State) (p q : Mode) (hq : u q = 0) :
    forcingCommutatorCell u forcing p q = 0 := by
  rw [forcingCommutatorCell, hq, helicalPlus_zero, helicalMinus_zero]
  funext j
  fin_cases j <;> simp [cross]

/-- Six-by-six mixed fold. -/
def sparseMixed (k : Mode) : Vec3 :=
  ∑ p in seedModes, ∑ q in seedModes,
    if Resonates p q k then mixedCell u₀ p q else 0

lemma mixed_sum_univ_eq_seed_left (k : Mode) :
    (∑ p : Mode, ∑ q : Mode,
      if Resonates p q k then mixedCell u₀ p q else 0) =
    ∑ p in seedModes, ∑ q : Mode,
      if Resonates p q k then mixedCell u₀ p q else 0 := by
  symm
  apply Finset.sum_subset (by simp)
  intro p hpUniv hpSeed
  have hp0 : u₀ p = 0 := u₀_zero_of_not_mem_seed hpSeed
  apply Finset.sum_eq_zero
  intro q hq
  by_cases hr : Resonates p q k
  · simp [hr, mixedCell_zero_left u₀ p q hp0]
  · simp [hr]

lemma mixed_sum_seed_eq_seed_seed (k : Mode) :
    (∑ p in seedModes, ∑ q : Mode,
      if Resonates p q k then mixedCell u₀ p q else 0) =
    sparseMixed k := by
  simp only [sparseMixed]
  apply Finset.sum_congr rfl
  intro p hp
  symm
  apply Finset.sum_subset (by simp)
  intro q hqUniv hqSeed
  have hq0 : u₀ q = 0 := u₀_zero_of_not_mem_seed hqSeed
  by_cases hr : Resonates p q k
  · simp [hr, mixedCell_zero_right u₀ p q hq0]
  · simp [hr]

/-- Literal fixed-output mixed product equals the six-by-six sparse fold. -/
theorem fixedOutputMixed_u₀_eq_sparse (k : Mode) :
    fixedOutputMixed u₀ k = sparseMixed k := by
  rw [fixedOutputMixed, mixed_sum_univ_eq_seed_left k,
      mixed_sum_seed_eq_seed_seed k]

lemma forcing₃₄₅_zero_of_not_mem_active
    {k : Mode} (hk : k ∉ activeOutputs) : forcing₃₄₅ k = 0 := by
  have hne :
      k ≠ k₁ ∧ k ≠ k₂ ∧ k ≠ k₃ ∧ k ≠ k₄ ∧
      k ≠ k₅ ∧ k ≠ k₆ ∧ k ≠ k₇ ∧ k ≠ k₈ := by
    simpa [activeOutputs, k₁, k₂, k₃, k₄, k₅, k₆, k₇, k₈] using hk
  rcases hne with ⟨h1,h2,h3,h4,h5,h6,h7,h8⟩
  simp [forcing₃₄₅, h1,h2,h3,h4,h5,h6,h7,h8]

/-- Eight-by-six commutator fold. -/
def sparseCommutator (k : Mode) : Vec3 :=
  ∑ p in activeOutputs, ∑ q in seedModes,
    if Resonates p q k then
      forcingCommutatorCell u₀ forcing₃₄₅ p q
    else 0

lemma comm_sum_univ_eq_active_left (k : Mode) :
    (∑ p : Mode, ∑ q : Mode,
      if Resonates p q k then
        forcingCommutatorCell u₀ forcing₃₄₅ p q
      else 0) =
    ∑ p in activeOutputs, ∑ q : Mode,
      if Resonates p q k then
        forcingCommutatorCell u₀ forcing₃₄₅ p q
      else 0 := by
  symm
  apply Finset.sum_subset (by simp)
  intro p hpUniv hpActive
  have hp0 : forcing₃₄₅ p = 0 :=
    forcing₃₄₅_zero_of_not_mem_active hpActive
  apply Finset.sum_eq_zero
  intro q hq
  by_cases hr : Resonates p q k
  · simp [hr, forcingCommutatorCell_zero_forcing u₀ forcing₃₄₅ p q hp0]
  · simp [hr]

lemma comm_sum_active_eq_active_seed (k : Mode) :
    (∑ p in activeOutputs, ∑ q : Mode,
      if Resonates p q k then
        forcingCommutatorCell u₀ forcing₃₄₅ p q
      else 0) =
    sparseCommutator k := by
  simp only [sparseCommutator]
  apply Finset.sum_congr rfl
  intro p hp
  symm
  apply Finset.sum_subset (by simp)
  intro q hqUniv hqSeed
  have hq0 : u₀ q = 0 := u₀_zero_of_not_mem_seed hqSeed
  by_cases hr : Resonates p q k
  · simp [hr, forcingCommutatorCell_zero_velocity
      u₀ forcing₃₄₅ p q hq0]
  · simp [hr]

/-- Literal fixed-output commutator equals the eight-by-six sparse fold. -/
theorem fixedOutputCommutator_u₀_eq_sparse (k : Mode) :
    fixedOutputCommutator u₀ (projectedNonlinearity u₀) k =
      sparseCommutator k := by
  rw [projectedNonlinearity_u₀_eq_forcing₃₄₅]
  rw [fixedOutputCommutator, comm_sum_univ_eq_active_left k,
      comm_sum_active_eq_active_seed k]

/-- Outside the eight seed-pair outputs the mixed factor vanishes, hence so
does the coherent-work row regardless of the commutator factor. -/
theorem sparseMixed_zero_of_not_mem_active
    {k : Mode} (hk : k ∉ activeOutputs) : sparseMixed k = 0 := by
  have hnotgen : k ∉ generatedOutputs := by
    simpa [generatedOutputs_eq_activeOutputs] using hk
  by_cases hz : isZeroMode k
  · -- No nonzero support claim is needed at zero; the seed-pair mixed fold
    -- cancels because no zero output is admitted by generatedOutputs.
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro q hq
    by_cases hr : Resonates p q k
    · have : k ∈ generatedOutputs := by
        simp [generatedOutputs, hz, p, hp, q, hq, hr]
      exact False.elim (hnotgen this)
    · simp [hr]
  · have hno :
        ¬ ∃ p ∈ seedModes, ∃ q ∈ seedModes, Resonates p q k := by
      intro hpair
      exact hnotgen (by simp [generatedOutputs, hz, hpair])
    apply Finset.sum_eq_zero
    intro p hp
    apply Finset.sum_eq_zero
    intro q hq
    have hnres : ¬ Resonates p q k := by
      intro hres
      exact hno ⟨p, hp, q, hq, hres⟩
    simp [sparseMixed, hnres]

end Rational345RealSnapshotHelicalSparse
end NSBControl
