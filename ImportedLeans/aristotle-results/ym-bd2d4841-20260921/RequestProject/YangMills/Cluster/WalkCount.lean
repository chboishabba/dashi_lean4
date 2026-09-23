/-
# Walk counting in a graph of bounded degree

This file proves the elementary but load-bearing combinatorial estimate behind the
outer (Kotecký–Preiss style) amplitude summation of the CMP116 cluster expansion:
in a graph all of whose degrees are at most `Δ`, the number of walks of a given
length starting at a given vertex is at most `Δ` to that length.

Everything here is a genuine theorem about Mathlib's `SimpleGraph.Walk`; nothing is
postulated.
-/
import Mathlib

open Finset

namespace RequestProject.YangMills.Cluster

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- In a graph with all degrees bounded by `Δ`, there are at most `Δ ^ n` walks of
length `n` from `u` to `v`.  This is the counting input to the outer domain sum. -/
theorem card_finsetWalkLength_le (G : SimpleGraph V) [G.LocallyFinite] (Δ : ℕ)
    (hΔ : ∀ x, G.degree x ≤ Δ) (n : ℕ) (u v : V) :
    #(G.finsetWalkLength n u v) ≤ Δ ^ n := by
  induction n generalizing u with
  | zero =>
    rcases eq_or_ne u v with rfl | h
    · simp [finsetWalkLength]
    · simp [finsetWalkLength, h]
  | succ n ih =>
    rw [finsetWalkLength]
    calc #(Finset.univ.biUnion fun (w : G.neighborSet u) =>
              (G.finsetWalkLength n w v).map ⟨fun p => Walk.cons w.property p, fun _ _ => by simp⟩)
        ≤ ∑ w : G.neighborSet u, #((G.finsetWalkLength n w v).map
              ⟨fun p => Walk.cons w.property p, fun _ _ => by simp⟩) := Finset.card_biUnion_le
      _ ≤ ∑ _w : G.neighborSet u, Δ ^ n := by
            refine Finset.sum_le_sum fun w _ => ?_
            rw [Finset.card_map]; exact ih _
      _ = G.degree u * Δ ^ n := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
              SimpleGraph.card_neighborSet_eq_degree]
      _ ≤ Δ * Δ ^ n := Nat.mul_le_mul_right _ (hΔ u)
      _ = Δ ^ (n + 1) := by ring

/-- The number of walks from `u` to `v` of length `< n` is at most `n * Δ ^ (n - 1)`
when `1 ≤ Δ`. -/
theorem card_finsetWalkLengthLT_le (G : SimpleGraph V) [G.LocallyFinite] (Δ : ℕ)
    (hΔ1 : 1 ≤ Δ) (hΔ : ∀ x, G.degree x ≤ Δ) (n : ℕ) (u v : V) :
    #(G.finsetWalkLengthLT n u v) ≤ n * Δ ^ (n - 1) := by
  have hcard : #(G.finsetWalkLengthLT n u v)
      = ∑ l ∈ Finset.range n, #(G.finsetWalkLength l u v) := by
    rw [finsetWalkLengthLT, Finset.card_disjiUnion]
  rw [hcard]
  calc ∑ l ∈ Finset.range n, #(G.finsetWalkLength l u v)
      ≤ ∑ _l ∈ Finset.range n, Δ ^ (n - 1) := by
        refine Finset.sum_le_sum fun l hl => ?_
        exact le_trans (card_finsetWalkLength_le G Δ hΔ l u v)
          (Nat.pow_le_pow_right hΔ1 (by simp only [Finset.mem_range] at hl; omega))
    _ = n * Δ ^ (n - 1) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

end RequestProject.YangMills.Cluster
