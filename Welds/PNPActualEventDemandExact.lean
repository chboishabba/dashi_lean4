import Welds.PNPChangingStabilizerExact
import Welds.PNPResidualAdaptiveTranscriptExact
import Welds.PNPFutureResidualChargeExact

namespace PNPActualEventDemand
open PNPHyperfabricOwnedEvents
open scoped BigOperators

-- A complete closed deterministic state cannot split after a collision.
-- Internal observations of that state are not independent oracle inputs.
theorem closed_collision {X S : Type*}
    (state : X → Nat → S) (advance : Nat → S → S)
    (exactStep : ∀ x k, state x (k+1) = advance k (state x k))
    (x y : X) (a len : Nat) (h : state x a = state y a) :
    state x (a+len) = state y (a+len) := by
  induction len with
  | zero => simpa using h
  | succ n ih =>
    rw [show a+(n+1)=a+n+1 by omega,exactStep x,exactStep y,ih]

theorem internal_observer_no_split {X S I : Type*}
    (state : X → Nat → S) (observe : Nat → X → I)
    (step : Nat → S → I → S)
    (readout : Nat → S → I)
    (obsExact : ∀ k x, observe k x = readout k (state x k))
    (stepExact : ∀ x k, state x (k+1) = step k (state x k) (observe k x))
    (x y : X) (a len : Nat) (h : state x a = state y a) :
    state x (a+len) = state y (a+len) := by
  apply closed_collision state (fun k s => step k s (readout k s)) _ x y a len h
  intro z k
  rw [stepExact,obsExact]

-- Actual finite event capacity permits OVERLAPPING epochs. The witness
-- event is still a real divergence on one anchor run, not a support count.
theorem capacity_bound {J : Type*} (O : Finset J) (w : J → Nat)
    (T C : Nat) (e : J → Fin T)
    (cap : ∀ k, (∑ j ∈ O.filter (fun j => e j=k), w j) ≤ C) :
    (∑ j ∈ O,w j) ≤ T*C := by
  classical
  have he : (∑ j ∈ O,w j) =
      ∑ k : Fin T, ∑ j ∈ O, if e j=k then w j else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    simp
  rw [he]
  calc
    (∑ k : Fin T, ∑ j ∈ O, if e j=k then w j else 0)
        = ∑ k : Fin T, ∑ j ∈ O.filter (fun j => e j=k), w j := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_filter]
    _ ≤ ∑ _k : Fin T, C := Finset.sum_le_sum (fun k _ => cap k)
    _ = T*C := by simp

-- Generalizes the disjoint-window injection to charged overlaps, but
-- does not construct superpolynomial demand or independently bound C.
theorem actual_event_capacity {X S I Y J : Type*}
    (valid : Set X) (state : X → Nat → S) (consumer : X → Y)
    (observe : Nat → X → I) (step : Nat → S → I → S)
    (stepExact : ∀ z k, state z (k+1)=step k (state z k) (observe k z))
    (x : X) (T C : Nat) (O : Finset J) (w : J → Nat)
    (a len : J → Nat) (rival : J → X)
    (hr : ∀ j, j∈O → rival j ∈ ReachableDivergentSet valid state consumer x (a j))
    (he : ∀ j, j∈O → state x (a j+len j) ≠ state (rival j) (a j+len j))
    (hT : ∀ j, j∈O → a j+len j≤T)
    (cap : ∀ k : Fin T, (∑ j ∈ O.filter
      (fun j => a j≤k.val ∧ k.val<a j+len j),w j) ≤ C) :
    (∑ j∈O,w j) ≤ T*C := by
  classical
  let J' := {j : J // j ∈ O}
  have existsEvent : ∀ j : J', ∃ k : Fin T, a j.val≤k.val ∧ k.val<a j.val+len j.val := by
    intro j
    obtain ⟨k,h₁,h₂,_,_,_⟩ := reachable_epoch_event valid state consumer
      observe step stepExact x (rival j.val) (a j.val) (len j.val)
      (hr j.val j.property) (he j.val j.property)
    exact ⟨⟨k,lt_of_lt_of_le h₂ (hT j.val j.property)⟩,h₁,h₂⟩
  -- Sum directly over window coverage: each obligation has an actual event,
  -- so has at least one paid coordinate. Capacities bound shared charges.
  calc
    (∑ j∈O,w j) ≤ ∑ j∈O, ∑ k : Fin T,
        if a j≤k.val ∧ k.val<a j+len j then w j else 0 := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨k,hk⟩ := existsEvent ⟨j,hj⟩
      have hle : (if a j≤k.val ∧ k.val<a j+len j then w j else 0) ≤
          ∑ k : Fin T, if a j≤k.val ∧ k.val<a j+len j then w j else 0 :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      simpa [hk] using hle
    _ = ∑ k : Fin T, ∑ j∈O, if a j≤k.val ∧ k.val<a j+len j then w j else 0 :=
      Finset.sum_comm
    _ ≤ ∑ _k : Fin T,C := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← Finset.sum_filter]
      exact cap k
    _ = T*C := by simp

-- No lower bound from mere distinct quotient fibres: if complete state
-- is equal, future internal events are equal. Any actual S1 producer must
-- expose a legitimate unresolved external input or a partial-state residual,
-- and independently justify capacity and unavoidable demand on actual work.
end PNPActualEventDemand
