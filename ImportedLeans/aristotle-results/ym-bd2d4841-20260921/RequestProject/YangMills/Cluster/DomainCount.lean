/-
# Counting connected localization domains

Combining the closed-tour theorem with the bounded-degree walk count gives the
entropy estimate that controls the outer `Σ_Y` sum of the CMP116 expansion: in a
graph of maximal degree `Δ`, there are at most `(2m+1) Δ ^ (2m)` connected domains of
cardinality `m+1` containing a prescribed source mark.

This is a genuine theorem: the domains are arbitrary connected finite vertex sets and
the bound is uniform in the volume.
-/
import RequestProject.YangMills.Cluster.WalkCount
import RequestProject.YangMills.Cluster.DomainTour

open Finset

namespace RequestProject.YangMills.Cluster

open SimpleGraph

variable {V : Type*} [DecidableEq V]

/-- **Entropy bound for connected domains.**  Any finite family of pairwise distinct
connected vertex sets of size `m + 1`, each containing the fixed mark `v`, has at most
`(2m+1) * Δ ^ (2m)` members, where `Δ` bounds the degrees of `G`. -/
theorem card_domains_le (G : SimpleGraph V) [G.LocallyFinite] (Δ : ℕ) (hΔ1 : 1 ≤ Δ)
    (hΔ : ∀ x, G.degree x ≤ Δ) (v : V) (m : ℕ) (𝒟 : Finset (Finset V))
    (h : ∀ Y ∈ 𝒟, v ∈ Y ∧ IsDomainConnected G Y ∧ #Y = m + 1) :
    #𝒟 ≤ (2 * m + 1) * Δ ^ (2 * m) := by
  classical
  have hex : ∀ Y : Finset V, ∃ w : G.Walk v v,
      Y ∈ 𝒟 → (w.support.toFinset = Y ∧ w.length < 2 * m + 1) := by
    intro Y
    by_cases hY : Y ∈ 𝒟
    · obtain ⟨hv, hconn, hcard⟩ := h Y hY
      obtain ⟨w, hws, hwl⟩ := exists_closed_tour hconn hv
      exact ⟨w, fun _ => ⟨hws, by omega⟩⟩
    · exact ⟨Walk.nil, fun hY' => absurd hY' hY⟩
  choose f hf using hex
  have hmaps : ∀ Y ∈ 𝒟, f Y ∈ G.finsetWalkLengthLT (2 * m + 1) v v := fun Y hY =>
    mem_finsetWalkLengthLT_iff.mpr (hf Y hY).2
  have hinj : ∀ Y ∈ 𝒟, ∀ Z ∈ 𝒟, f Y = f Z → Y = Z := by
    intro Y hY Z hZ hfe
    rw [← (hf Y hY).1, ← (hf Z hZ).1, hfe]
  calc #𝒟 ≤ #(G.finsetWalkLengthLT (2 * m + 1) v v) :=
        Finset.card_le_card_of_injOn f hmaps hinj
    _ ≤ (2 * m + 1) * Δ ^ (2 * m + 1 - 1) :=
        card_finsetWalkLengthLT_le G Δ hΔ1 hΔ (2 * m + 1) v v
    _ = (2 * m + 1) * Δ ^ (2 * m) := by norm_num

end RequestProject.YangMills.Cluster
