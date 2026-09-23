/-
# B3: per-domain tree localization

This file proves the per-domain CMP116 tree bound

  `commonYShell Y ≤ A_Y * W d_Y`,   `W d = η ^ d`,

for the literal decomposition in which the surviving differentiated terms of a
localization domain `Y` are indexed by connecting walks (trees) between the two
source marks whose support is exactly `Y`, and each term majorant is an amplitude
times `(η*η)` to the length of the connecting walk.

The two geometric facts that make the bound work are proved here, not assumed:

* a connecting walk whose support is `Y` has at least `#Y - 1` edges, so half of the
  activity weight pays for the *volume* of the domain — this is what makes the outer
  sum of `A_Y` summable (see `AmplitudeSummability`);
* a connecting walk between the marks has at least `G.dist a b` edges, so the other
  half pays for the *distance* between the marks.

Consequently `A_Y` carries the factor `η ^ (#Y - 1)` and the extracted decay weight is
the genuine graph distance between the two source marks.
-/
import RequestProject.YangMills.Cluster.DomainTour

open Finset

namespace RequestProject.YangMills.Cluster

open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A walk spanning `Y` has at least `#Y - 1` edges. -/
theorem card_le_length_succ {a b : V} (w : G.Walk a b) {Y : Finset V}
    (hspan : Y ⊆ w.support.toFinset) : #Y ≤ w.length + 1 := by
  calc #Y ≤ #w.support.toFinset := Finset.card_le_card hspan
    _ ≤ w.support.length := List.toFinset_card_le _
    _ = w.length + 1 := w.length_support

/-- **B3, per-domain tree localization.**  With `0 ≤ η ≤ 1`, if every surviving term
of the domain `Y` is carried by a connecting walk between the marks `a` and `b` whose
support spans `Y` and whose length is at least `d`, then the total term majorant of the
domain is bounded by `A_Y * η ^ d` with
`A_Y = (∑ amplitudes) * η ^ (#Y - 1)`. -/
theorem per_domain_tree_localization {ι : Type*} (Y : Finset V) {a b : V}
    (T : Finset ι) (wt : ι → G.Walk a b) (amp : ι → ℝ) (hamp : ∀ t ∈ T, 0 ≤ amp t)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hspan : ∀ t ∈ T, Y ⊆ (wt t).support.toFinset)
    (d : ℕ) (hd : ∀ t ∈ T, d ≤ (wt t).length) :
    ∑ t ∈ T, amp t * (η * η) ^ (wt t).length
      ≤ ((∑ t ∈ T, amp t) * η ^ (#Y - 1)) * η ^ d := by
  have hstep : ∀ t ∈ T, amp t * (η * η) ^ (wt t).length
      ≤ amp t * (η ^ (#Y - 1) * η ^ d) := by
    intro t ht
    have hvol : #Y - 1 ≤ (wt t).length := by
      have := card_le_length_succ (wt t) (hspan t ht)
      omega
    have h1 : η ^ (wt t).length ≤ η ^ (#Y - 1) := pow_le_pow_of_le_one hη0 hη1 hvol
    have h2 : η ^ (wt t).length ≤ η ^ d := pow_le_pow_of_le_one hη0 hη1 (hd t ht)
    have hpow : (η * η) ^ (wt t).length = η ^ (wt t).length * η ^ (wt t).length := by
      rw [mul_pow]
    rw [hpow]
    refine mul_le_mul_of_nonneg_left ?_ (hamp t ht)
    exact mul_le_mul h1 h2 (pow_nonneg hη0 _) (pow_nonneg hη0 _)
  calc ∑ t ∈ T, amp t * (η * η) ^ (wt t).length
      ≤ ∑ t ∈ T, amp t * (η ^ (#Y - 1) * η ^ d) := Finset.sum_le_sum hstep
    _ = ((∑ t ∈ T, amp t) * η ^ (#Y - 1)) * η ^ d := by
        rw [← Finset.sum_mul]; ring

/-- The distance version: the extracted decay weight can be taken at the genuine graph
distance between the two source marks, with no extra hypothesis. -/
theorem per_domain_tree_localization_dist {ι : Type*} (Y : Finset V) {a b : V}
    (T : Finset ι) (wt : ι → G.Walk a b) (amp : ι → ℝ) (hamp : ∀ t ∈ T, 0 ≤ amp t)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hspan : ∀ t ∈ T, Y ⊆ (wt t).support.toFinset) :
    ∑ t ∈ T, amp t * (η * η) ^ (wt t).length
      ≤ ((∑ t ∈ T, amp t) * η ^ (#Y - 1)) * η ^ G.dist a b :=
  per_domain_tree_localization Y T wt amp hamp η hη0 hη1 hspan (G.dist a b)
    (fun t _ => SimpleGraph.dist_le (wt t))

omit [DecidableEq V] in
/-- The selected physical distance never exceeds the domain (tree) distance: any
length occurring among the connecting walks dominates `G.dist a b`. -/
theorem dist_le_of_term_length {a b : V} {ι : Type*} (wt : ι → G.Walk a b) (t : ι) :
    G.dist a b ≤ (wt t).length := SimpleGraph.dist_le (wt t)

end RequestProject.YangMills.Cluster
