import Welds.PNPResidualGeometryBridgeExact
import Welds.PNPEpochChargeExact

namespace PNPHyperfabricEpochEvent
open PNPSameRunReadFootprint PNPResidualGeometryBridge

-- First divergence is on an actual finite run, not on a hypothetical
-- intermediate consumer that an arbitrary correct algorithm must compute.
theorem first_divergence {S : Type*} (x y : Nat → S) (n : Nat)
    (h0 : x 0 = y 0) (hn : x n ≠ y n) :
    ∃ k < n, x k = y k ∧ x (k+1) ≠ y (k+1) := by
  induction n with
  | zero => exact False.elim (hn h0)
  | succ n ih =>
    by_cases h : x n = y n
    · exact ⟨n, Nat.lt_succ_self n, h, hn⟩
    · obtain ⟨k,hk,he,hd⟩ := ih h
      exact ⟨k,Nat.lt_trans hk (Nat.lt_succ_self n),he,hd⟩

-- At a first divergence, identical prior complete states and identical
-- observations would force identical next states. A genuine event receipt
-- records the distinguishing observation; erasure alone proves nothing.
theorem event_observation {X S I : Type*} (step : Nat → S → I → S)
    (observe : Nat → X → I) (runState : X → Nat → S) (x y : X) (n : Nat)
    (stepExact : ∀ z k, runState z (k+1) = step k (runState z k) (observe k z))
    (h0 : runState x 0 = runState y 0)
    (hn : runState x n ≠ runState y n) :
    ∃ k < n, runState x k = runState y k ∧
      runState x (k+1) ≠ runState y (k+1) ∧ observe k x ≠ observe k y := by
  obtain ⟨k,hk,he,hd⟩ := first_divergence (runState x) (runState y) n h0 hn
  refine ⟨k,hk,he,hd,?_⟩
  intro eq
  apply hd
  rw [stepExact x k,stepExact y k,he,eq]

-- Attach each retained minimal support to the existing actual adaptive
-- epoch theorem. This needs a representative reachable alternative for
-- EACH retained support, with actual start collision and end separation.
theorem epoch_support_hit {S : Type*} [DecidableEq S] {n : Nat}
    (ask : S → Option (Fin n × (Bool → S)))
    (prefix : (Fin n → Bool) → S) (x y : Fin n → Bool)
    (fuel : Nat) (support : Finset (Fin n))
    (exactSupport : ∀ i, i ∈ support ↔ x i ≠ y i)
    (collision : prefix x = prefix y)
    (separated : (run ask x fuel (prefix x)).1 ≠ (run ask y fuel (prefix y)).1) :
    ∃ i ∈ (run ask x fuel (prefix x)).2, i ∈ support := by
  obtain ⟨i,hr,hd⟩ := PNPEpochCharge.separated_epoch ask prefix x y fuel collision separated
  exact ⟨i,hr,(exactSupport i).mpr hd⟩

-- Removing a superset is valid only when the actual smaller support is
-- retained with its own event evidence; it cannot create new collisions.
theorem hit_superset {I : Type*} (a b : Finset I) (R : List I)
    (sub : a ⊆ b) (h : ∃ i ∈ R, i ∈ a) : ∃ i ∈ R, i ∈ b := by
  obtain ⟨i,hi,ha⟩ := h
  exact ⟨i,hi,sub ha⟩

end PNPHyperfabricEpochEvent
