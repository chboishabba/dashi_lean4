import Welds.PNPActualEventDemandExact
import Welds.PNPSameRunReadFootprintExact
import Welds.PNPActualInstructionLedgerExact

namespace PNPQuotientDemandBoundary
open scoped BigOperators

-- An expander incidence design with bounded degree is still bounded by
-- the number of original coordinates. Weights may be arbitrary Nat.
theorem sparse_input_ceiling {J : Type*} {n : Nat}
    (O : Finset J) (D : J → Finset (Fin n)) (w : J → Nat) (C : Nat)
    (nonempty : ∀ j ∈ O, (D j).Nonempty)
    (capacity : ∀ i : Fin n, (∑ j ∈ O, if i ∈ D j then w j else 0) ≤ C) :
    (∑ j ∈ O,w j) ≤ n*C := by
  classical
  calc
    (∑ j ∈ O,w j) ≤ ∑ j ∈ O, ∑ i : Fin n, if i ∈ D j then w j else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨i,hi⟩ := nonempty j hj
      have h := Finset.single_le_sum (s := Finset.univ)
        (f := fun i : Fin n => if i ∈ D j then w j else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      simpa [hi] using h
    _ = ∑ i : Fin n, ∑ j ∈ O, if i ∈ D j then w j else 0 := Finset.sum_comm
    _ ≤ ∑ _i : Fin n,C := Finset.sum_le_sum (fun i _ => capacity i)
    _ = n*C := by simp

-- A complete exact verifier of an EXPLICIT tableau has to read every
-- individually sensitive bit on the accepted assignment. Formula
-- serialization seek is not a read of an assignment to that formula.
theorem tableau_sensitive_reads {S : Type*} {n : Nat}
    (ask : S → Option (Fin n × (Bool → S))) (accept : S → Bool)
    (valid : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (k : Nat) (s : S) (sensitive : Finset (Fin n))
    (correct : ∀ y, accept (PNPSameRunReadFootprint.run ask y k s).1 = valid y)
    (h : ∀ i ∈ sensitive, valid x ≠ valid (PNPSameRunReadFootprint.flip x i)) :
    sensitive.card ≤ k := by
  apply (PNPSameRunReadFootprint.sensitive_set_lower ask accept x k s sensitive ?_).trans
    (PNPSameRunReadFootprint.reads_le_fuel ask x k s)
  intro i hi
  rw [correct,correct]
  exact h i hi

theorem unique_tableau_reads {S : Type*} {n : Nat}
    (ask : S → Option (Fin n × (Bool → S))) (accept : S → Bool)
    (valid : (Fin n → Bool) → Bool) (x : Fin n → Bool)
    (k : Nat) (s : S)
    (correct : ∀ y, accept (PNPSameRunReadFootprint.run ask y k s).1 = valid y)
    (yes : valid x = true)
    (unique : ∀ y, valid y = true → y = x) : n ≤ k := by
  classical
  apply PNPSameRunReadFootprint.all_sensitive_lower ask accept x k s
  intro i he
  rw [correct,correct,yes] at he
  have eq := unique _ he.symm
  have e := congrFun eq i
  cases hx : x i <;> simp [PNPSameRunReadFootprint.flip,hx] at e

-- All overhead must fit the same actual physical horizon. These are
-- necessary inequalities; no zero-edge or shortcut producer assumed.
theorem stutter_overhead (T source zeros positive mid setup query resume suffix : Nat)
    (partition : source = zeros+positive)
    (width : 2*T ≤ source) (paid : positive ≤ mid)
    (fits : setup+query+mid+resume+suffix ≤ T) :
    T+setup+query+resume+suffix ≤ zeros := by omega

theorem full_read_no_positive_horizon (T sensitive queries other : Nat)
    (width : 2*T ≤ sensitive) (verified : sensitive ≤ queries)
    (fits : queries+other ≤ T) : T=0 := by omega

-- The exact explicit-tableau read lower bound is not a lower bound on
-- SAT or on structured/implicit witnesses. Likewise, sparse supports
-- cannot create an unbounded number of fresh internal observations of
-- a complete closed state. Both routes must preserve the original model.
end PNPQuotientDemandBoundary
