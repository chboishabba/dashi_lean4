import Welds.PNPOriginalAnchoredInputOnlyCeilingNoGoExact
import Welds.PNPOriginalActualEventTimeInverseExact

/-!
Section 36 — SAME original anchored F3 obligation ledger:
input-only capacity vs actual same-run work capacity.

This reconciles the two existing genuine source-owner theorems,
rather than promoting the number of algebraic rivals into physical
computation time. It gives a falsifiable no-go for any claimed
input-only superlinear demand, even if the same obligations also have
a valid physical event-window representation.

The true original universal SAT work producer remains open. Nothing
below assumes that an arbitrary SAT algorithm admits this representation.
-/
namespace PNPOriginalResidualFutureReadWeld
open PNPResidualGeometryBridge PNPLinearConsumerCut
open PNPF3SyndromeBoundary PNPSameRunReadFootprint
open PNPActualEventDemand
open PNPHyperfabricOwnedEvents
open scoped BigOperators

/-- For the EXACT original weighted F3 anchored rivals, a legal
input-coordinate capacity certificate already imposes a ceiling
W <= n*C_input. Any alleged original same-obligation superlinear
demand above that ceiling contradicts the source input-only model.
No machine cost is inferred from W alone. -/
theorem original_anchored_input_only_cannot_exceed_capacity
    {n : Nat} {J : Type*} [DecidableEq J]
    (x : Fin n → Bool)
    (O : Finset J) (direction : J → Syndrome n)
    (weight : J → Nat) (C_input : Nat)
    (hchange : ∀ j ∈ O,
      ∃ i : Fin n, x i ≠ reopen x (direction j) i)
    (hinput : ∀ i : Fin n,
      (∑ j ∈ O,
        if x i ≠ reopen x (direction j) i then weight j else 0)
          ≤ C_input)
    (hfake : n * C_input < ∑ j ∈ O, weight j) : False := by
  have hceiling :=
    original_anchored_input_only_capacity_ceiling
      x O direction weight C_input hchange hinput
  exact (not_lt_of_ge hceiling) hfake

/-- The same original O, weight ledger, source x and source
signed F3 directions may be accounted in *both* ledgers.
This is a bounded interface, not a discovery of physical
work from the input-only supports.

The first conclusion is the pre-existing original input
ceiling. The second is actual-event time payment, using the
original dynamic reachable and divergent observer contract.
-/
theorem original_anchored_dual_capacity_same_obligations
    {n : Nat} {S I Y J : Type*} [DecidableEq J]
    (x : Fin n → Bool)
    (direction : J → Syndrome n)
    (O : Finset J) (weight : J → Nat)
    (C_input : Nat)
    (hchange : ∀ j ∈ O,
      ∃ i : Fin n, x i ≠ reopen x (direction j) i)
    (hinput : ∀ i : Fin n,
      (∑ j ∈ O,
        if x i ≠ reopen x (direction j) i then weight j else 0)
          ≤ C_input)
    (valid : Set (Fin n → Bool))
    (state : (Fin n → Bool) → Nat → S)
    (consumer : (Fin n → Bool) → Y)
    (observe : Nat → (Fin n → Bool) → I)
    (step : Nat → S → I → S)
    (stepExact : ∀ z k,
      state z (k+1) = step k (state z k) (observe k z))
    (T C_event : Nat)
    (a len : J → Nat)
    (hr : ∀ j, j ∈ O,
      reopen x (direction j) ∈
        ReachableDivergentSet valid state consumer x (a j))
    (he : ∀ j, j ∈ O,
      state x (a j+len j) ≠
        state (reopen x (direction j)) (a j+len j))
    (hT : ∀ j, j ∈ O, a j+len j ≤ T)
    (hcap : ∀ k : Fin T,
      (∑ j ∈ O.filter
        (fun j => a j ≤ k.val ∧ k.val < a j+len j),
        weight j) ≤ C_event) :
    (∑ j ∈ O, weight j) ≤ n * C_input ∧
    (∑ j ∈ O, weight j) ≤ T * C_event := by
  constructor
  · exact original_anchored_input_only_capacity_ceiling
      x O direction weight C_input hchange hinput
  · exact actual_event_capacity valid state consumer
      observe step stepExact x T C_event O weight a len
      (fun j => reopen x (direction j)) hr he hT hcap

end PNPOriginalResidualFutureReadWeld
