import Mathlib
import Welds.PNPHyperfabricEpochEventExact
import Welds.PNPPrimeValuationPriorityExact
import Welds.PNPStackPriorityTransportExact

namespace PNPHyperfabricOwnedEvents

def ReachableDivergentSet {X S Y : Type*}
    (valid : Set X) (state : X → Nat → S) (consumer : X → Y)
    (x : X) (t : Nat) : Set X :=
  {y | y ∈ valid ∧ state y t = state x t ∧ consumer y ≠ consumer x}

-- A reachable alternative is relevant to the actual consumer. To charge
-- an epoch it must also separate at its actual end, not merely eventually.
theorem reachable_epoch_event {X S I Y : Type*}
    (valid : Set X) (state : X → Nat → S) (consumer : X → Y)
    (observe : Nat → X → I) (step : Nat → S → I → S)
    (stepExact : ∀ z k, state z (k+1) = step k (state z k) (observe k z))
    (x y : X) (a len : Nat)
    (hy : y ∈ ReachableDivergentSet valid state consumer x a)
    (hend : state x (a+len) ≠ state y (a+len)) :
    ∃ j, a ≤ j ∧ j < a+len ∧ state x j = state y j ∧
      state x (j+1) ≠ state y (j+1) ∧ observe j x ≠ observe j y := by
  have hstart : state y a = state x a := hy.2.1
  obtain ⟨k,hk,he,hd⟩ := PNPHyperfabricEpochEvent.first_divergence
    (fun k => state x (a+k)) (fun k => state y (a+k)) len
    (by simpa using hstart.symm) hend
  refine ⟨a+k, by omega, by omega, he, ?_, ?_⟩
  · simpa [Nat.add_assoc] using hd
  · intro eq
    apply hd
    rw [← Nat.add_assoc,stepExact x (a+k),stepExact y (a+k),he,eq]

-- Event IDs are actual time positions on ONE anchor run.
-- Disjoint time windows imply non-reuse even for repeated input addresses.
theorem event_windows_disjoint (a b c d i j : Nat)
    (hi : a ≤ i ∧ i < b) (hj : c ≤ j ∧ j < d) (hbc : b ≤ c) :
    i ≠ j := by omega

theorem fresh_insert_card (paid : Finset Nat) (j : Nat)
    (fresh : j ∉ paid) : (insert j paid).card = paid.card + 1 := by
  simp [fresh]

-- Single-use original coordinates can never supply more than n charges.
theorem input_support_ceiling {n : Nat} (paid : Finset (Fin n)) :
    paid.card ≤ n := by
  simpa using (Finset.card_le_univ paid)

end PNPHyperfabricOwnedEvents

namespace PNPActualLaneAllocation

-- Finite emitted inventory is the owner: five data indices and all
-- actual control/private tag indices. Enumerate the primes, not lanes
-- from a different compiler.
noncomputable def allocLanePrime (i : Nat) : Nat := Nat.nth Nat.Prime i

theorem alloc_prime (i : Nat) : Nat.Prime (allocLanePrime i) := by
  unfold allocLanePrime
  exact?

theorem alloc_injective : Function.Injective allocLanePrime := by
  unfold allocLanePrime
  exact?

theorem alloc_pairwise : Pairwise (fun i j => Nat.Coprime (allocLanePrime i) (allocLanePrime j)) := by
  intro i j hij
  have hne : allocLanePrime i ≠ allocLanePrime j := fun e => hij (alloc_injective e)
  have hi := alloc_prime i
  have hj := alloc_prime j
  exact?

end PNPActualLaneAllocation
