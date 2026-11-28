import Mathlib
import Welds.PNPMultiCutCrossingExact

namespace PNPPaidCutCapacity
open scoped BigOperators

-- A paid event can carry several obligations, but its total declared
-- charge is bounded by its actual capacity. This is the missing premise
-- that a W-bit state alone does NOT supply for arbitrary virtual cuts.
theorem weighted_same_run {A C M : Type*} [Fintype A] [Fintype C] [Fintype M]
    (words : C → A → List M) (inj : ∀ c, Function.Injective (words c))
    (time : A → Nat) (W K : Nat) (charge : C → A → Nat → Nat)
    (capacity : ∀ x e, (∑ c, charge c x e) ≤ W)
    (lengthBound : ∀ c x,
      (words c x).length ≤ (∑ e ∈ Finset.range (time x), charge c x e)+1)
    (large : Fintype.card C * (Fintype.card M+1)^K < Fintype.card A) :
    ∃ x, Fintype.card C*K ≤ time x*W := by
  apply PNPMultiCutCrossing.same_run_lower words inj
    (fun c x => ∑ e ∈ Finset.range (time x), charge c x e)
    (fun x => time x*W) _ lengthBound K large
  intro x
  calc
    (∑ c, ∑ e ∈ Finset.range (time x), charge c x e)
      = ∑ e ∈ Finset.range (time x), ∑ c, charge c x e := Finset.sum_comm
    _ ≤ ∑ _e ∈ Finset.range (time x), W := by
      apply Finset.sum_le_sum
      intro e _
      exact capacity x e
    _ = time x*W := by simp

-- Exact two-block equality has 2^n different rows, yet paired random
-- access computes it with one accumulated equality bit and a counter.
-- This retires a rank-only or mutual-information-only time-space claim.
def pairScan : List Bool → List Bool → Bool
  | [], [] => true
  | x::xs, y::ys => (x == y) && pairScan xs ys
  | _, _ => false

theorem pairScan_exact (xs ys : List Bool) :
    pairScan xs ys = true ↔ xs=ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [pairScan]
  | cons x xs ih =>
    cases ys with
    | nil => simp [pairScan]
    | cons y ys => simp [pairScan,ih]

theorem equality_rows {A : Type*} :
    Function.Injective (fun x : A => fun y : A => x=y) := by
  intro x y h
  have e := congrFun h x
  exact (Eq.mp e rfl).symm

theorem equality_row_count (n : Nat) :
    Fintype.card (Fin n → Bool)=2^n := by simp

-- On the real RAM/streaming layout, paired reads do not have to keep
-- distinct transcripts for r blocks concurrently. The accumulator
-- suffices for the single decision; it is not a lossless input encoder.
-- A random-access lower bound must supply the capacity premise on
-- actual non-reusable messages, not assume it from input partitioning.
end PNPPaidCutCapacity
