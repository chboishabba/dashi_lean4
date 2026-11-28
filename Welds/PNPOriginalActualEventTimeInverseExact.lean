import Welds.PNPActualEventDemandExact

/-!
Section35: reverse-solve of the ACTUAL same-run event capacity contract.

This is the physical time consequence of an *actual verified* obligation
producer, with all overlapping epochs charged to the same execution.
Nothing here manufactures exponential demand from input geometry.
The precise open universal premise is now the actual-event mass > B*C,
not an informal "number of rivals" argument.

The source uses the existing ReachableDivergentSet and
actual_event_capacity theorem; no fresh synthetic oracle is introduced.
-/
namespace PNPActualEventDemand
open PNPHyperfabricOwnedEvents
open scoped BigOperators

/-- If the genuinely observed same-run obligations carry more total
weight than B time slots can process at capacity C, the actual
execution must have STRICTLY MORE than B slots. All original event
ownership/fidelity premises remain explicit and unchanged. -/
theorem actual_original_event_demand_forces_time_beyond
    {X S I Y J : Type*}
    (valid : Set X) (state : X → Nat → S) (consumer : X → Y)
    (observe : Nat → X → I) (step : Nat → S → I → S)
    (stepExact : ∀ z k, state z (k+1) =
      step k (state z k) (observe k z))
    (x : X) (T C B : Nat)
    (O : Finset J) (w : J → Nat)
    (a len : J → Nat) (rival : J → X)
    (hr : ∀ j, j ∈ O →
      rival j ∈ ReachableDivergentSet valid state consumer x (a j))
    (he : ∀ j, j ∈ O →
      state x (a j + len j) ≠
        state (rival j) (a j + len j))
    (hT : ∀ j, j ∈ O → a j + len j ≤ T)
    (cap : ∀ k : Fin T,
      (∑ j ∈ O.filter (fun j =>
        a j ≤ k.val ∧ k.val < a j + len j), w j) ≤ C)
    (hdemand : B * C < ∑ j ∈ O, w j) :
    B < T := by
  have hpaid : (∑ j ∈ O, w j) ≤ T*C :=
    actual_event_capacity valid state consumer observe step
      stepExact x T C O w a len rival hr he hT cap
  by_contra hnot
  have ht : T ≤ B := Nat.le_of_not_gt hnot
  have hcap : T*C ≤ B*C := Nat.mul_le_mul_right C ht
  omega

/-- If an alleged actual anchored event certificate has positive
total mass, both time and per-time capacity must be positive.
This catches impossible zero-capacity / zero-time promotions in
every event-demand receipt. -/
theorem actual_original_positive_demand_requires_live_clock
    {X S I Y J : Type*}
    (valid : Set X) (state : X → Nat → S) (consumer : X → Y)
    (observe : Nat → X → I) (step : Nat → S → I → S)
    (stepExact : ∀ z k, state z (k+1) =
      step k (state z k) (observe k z))
    (x : X) (T C : Nat) (O : Finset J) (w : J → Nat)
    (a len : J → Nat) (rival : J → X)
    (hr : ∀ j, j ∈ O →
      rival j ∈ ReachableDivergentSet valid state consumer x (a j))
    (he : ∀ j, j ∈ O →
      state x (a j + len j) ≠
        state (rival j) (a j + len j))
    (hT : ∀ j, j ∈ O → a j + len j ≤ T)
    (cap : ∀ k : Fin T,
      (∑ j ∈ O.filter (fun j =>
        a j ≤ k.val ∧ k.val < a j + len j), w j) ≤ C)
    (hpositive : 0 < ∑ j ∈ O, w j) :
    0 < T ∧ 0 < C := by
  have hpaid := actual_event_capacity valid state consumer
    observe step stepExact x T C O w a len rival hr he hT cap
  constructor
  · by_contra h0
    have hT0 : T = 0 := Nat.eq_zero_of_not_pos h0
    simp [hT0] at hpaid
    omega
  · by_contra h0
    have hC0 : C = 0 := Nat.eq_zero_of_not_pos h0
    simp [hC0] at hpaid
    omega

end PNPActualEventDemand
