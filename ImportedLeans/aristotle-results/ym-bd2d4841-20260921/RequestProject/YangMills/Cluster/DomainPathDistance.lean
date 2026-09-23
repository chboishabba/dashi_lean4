/-
# The connected-core path geometry: `d_graph(J_L, J_R) ≤ d_k(Y)`

This is the second half of the one-sided geometry payment of the selected CMP116
localization (item `B3` of the Goal-1 backlog): the connected localization domain `Y`
carrying a differentiated term contains a walk joining the two source marks, and that
walk is no longer than the domain's own tree distance.  Consequently the graph distance
between the marks — the exponent that the cluster estimate produces — is bounded by the
domain size, and the source weight evaluated at `d_k(Y)` dominates the weight evaluated
at the mark separation.

Nothing is assumed about how `Y` arose: domain connectedness (the notion of
`Cluster/DomainTour.lean`, which is proved there to coincide with "every vertex is
joined to the base point inside `Y`") is the only input, and the bound

  `d_graph(a, b) + 1 ≤ #Y`

is proved by bypassing an internal walk to a path, whose support is duplicate free and
contained in `Y`.
-/
import RequestProject.YangMills.Cluster.DomainTour

namespace RequestProject.YangMills.Cluster

open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A walk that stays inside a finite set `Y` bounds the graph distance of its
endpoints by `#Y - 1`: bypassing it produces a path, whose support is duplicate free
and still contained in `Y`. -/
theorem dist_succ_le_card_of_walk_within {Y : Finset V} {a b : V} (p : G.Walk a b)
    (hp : ∀ u ∈ p.support, u ∈ Y) : G.dist a b + 1 ≤ Y.card := by
  have hpath := p.bypass_isPath
  have hsub : ∀ u ∈ p.bypass.support, u ∈ Y := fun u hu => hp u (Walk.support_bypass_subset p hu)
  have hd : G.dist a b ≤ p.bypass.length := SimpleGraph.dist_le _
  have hcard : p.bypass.support.toFinset.card = p.bypass.length + 1 := by
    rw [List.toFinset_card_of_nodup hpath.support_nodup, Walk.length_support]
  have hsubset : p.bypass.support.toFinset ⊆ Y :=
    fun u hu => hsub u (List.mem_toFinset.mp hu)
  have := Finset.card_le_card hsubset
  omega

/-- **The connected-core path geometry.**  In a domain-connected localization domain `Y`
containing both source marks, the graph distance between the marks is at most the domain
tree distance `d_k(Y) = #Y - 1`. -/
theorem dist_succ_le_card_of_domainConnected {Y : Finset V} (hconn : IsDomainConnected G Y)
    {a b : V} (ha : a ∈ Y) (hb : b ∈ Y) : G.dist a b + 1 ≤ Y.card := by
  obtain ⟨p, hp⟩ := reachable_within_of_isDomainConnected hconn ha hb
  exact dist_succ_le_card_of_walk_within p hp

/-- The two marks of a domain-connected domain are joined in the ambient graph. -/
theorem reachable_of_domainConnected {Y : Finset V} (hconn : IsDomainConnected G Y)
    {a b : V} (ha : a ∈ Y) (hb : b ∈ Y) : G.Reachable a b := by
  obtain ⟨p, _⟩ := reachable_within_of_isDomainConnected hconn ha hb
  exact ⟨p⟩

/-- **The source weight at `d_k(Y)` dominates the weight at the mark separation.**  This
is the form in which the previous theorem is consumed: a geometric source weight
evaluated at the domain tree distance is an upper bound for the same weight evaluated at
the graph distance of the two marks, so a per-domain estimate stated with `d_k(Y)`
implies the estimate with the separation of the sources. -/
theorem pow_card_le_pow_dist {Y : Finset V} (hconn : IsDomainConnected G Y) {a b : V}
    (ha : a ∈ Y) (hb : b ∈ Y) {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    η ^ (Y.card - 1) ≤ η ^ (G.dist a b) := by
  have h := dist_succ_le_card_of_domainConnected hconn ha hb
  exact pow_le_pow_of_le_one h0 h1 (by omega)

end RequestProject.YangMills.Cluster

/-! ## Axiom audit -/

section Audit

open RequestProject.YangMills.Cluster

#print axioms dist_succ_le_card_of_domainConnected
#print axioms pow_card_le_pow_dist

end Audit
