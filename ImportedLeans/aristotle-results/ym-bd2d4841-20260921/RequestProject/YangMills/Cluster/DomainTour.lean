/-
# Closed tours of a connected expansion domain

The outer (`Σ_Y`) sum of the CMP116 expansion runs over *connected* localization
domains `Y` containing a fixed source mark.  To count such domains one needs the
classical fact that a connected set of `n` vertices carries a closed tour of length
at most `2 (n - 1)` visiting exactly that set.  That is what this file proves, from
scratch, for Mathlib's `SimpleGraph`.

The connectivity hypothesis is stated in its combinatorial ("no separating subset")
form `IsDomainConnected`, and `isDomainConnected_iff_reachable_within` proves that
this is *exactly* the usual notion: every vertex of `Y` is joined to the base point
by a walk staying inside `Y`.  So the counting theorem is about genuine connected
domains, not about a convenient surrogate.
-/
import Mathlib

open Finset

namespace RequestProject.YangMills.Cluster

open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A finite vertex set `Y` is *domain connected* when no proper nonempty subset of
`Y` is separated from the rest of `Y`: some edge of `G` leaves every such subset
inside `Y`. -/
def IsDomainConnected (G : SimpleGraph V) (Y : Finset V) : Prop :=
  ∀ S : Finset V, S ⊆ Y → S.Nonempty → S ≠ Y → ∃ x ∈ S, ∃ y ∈ Y, y ∉ S ∧ G.Adj x y

section Surgery

/-- Walk surgery: a closed walk through `x` can be extended by a return trip along an
edge `x ~ y`, adding the single vertex `y` to its support and `2` to its length. -/
theorem exists_detour {v x y : V} (w : G.Walk v v) (hx : x ∈ w.support) (hxy : G.Adj x y) :
    ∃ w' : G.Walk v v, w'.support.toFinset = insert y w.support.toFinset ∧
      w'.length = w.length + 2 := by
  set p := w.takeUntil x hx with hp
  set q := w.dropUntil x hx with hq
  have hspec : p.append q = w := w.take_spec hx
  refine ⟨p.append (Walk.cons hxy (Walk.cons hxy.symm q)), ?_, ?_⟩
  · have hxp : x ∈ p.support := Walk.end_mem_support p
    rw [← hspec]
    ext z
    simp only [Walk.support_append, List.toFinset_append, Finset.mem_union, Finset.mem_insert,
      List.mem_toFinset, Walk.support_cons, List.tail_cons]
    constructor
    · rintro (h | h)
      · exact Or.inr (Or.inl h)
      · simp only [List.mem_cons] at h
        rcases h with rfl | h
        · exact Or.inl rfl
        · rcases List.mem_cons.mp (by rwa [← Walk.support_eq_cons q]) with rfl | h'
          · exact Or.inr (Or.inl (by simp [hxp]))
          · exact Or.inr (Or.inr h')
    · rintro (rfl | h | h)
      · exact Or.inr (by simp)
      · exact Or.inl h
      · exact Or.inr (by simp [List.mem_cons, List.mem_of_mem_tail h])
  · rw [Walk.length_append, ← hspec, Walk.length_append]
    simp only [Walk.length_cons]
    omega

end Surgery

/-- Growth step: from a closed tour of a proper subset `S` of a domain-connected `Y`
one reaches a closed tour of all of `Y`, still of length `≤ 2 (#Y - 1)`. -/
theorem exists_tour_of_subset (Y : Finset V) (hconn : IsDomainConnected G Y) :
    ∀ k : ℕ, ∀ (S : Finset V) (v : V) (w : G.Walk v v),
      #(Y \ S) ≤ k → S ⊆ Y → w.support.toFinset = S → w.length + 2 ≤ 2 * #S →
      ∃ w' : G.Walk v v, w'.support.toFinset = Y ∧ w'.length + 2 ≤ 2 * #Y := by
  intro k
  induction k with
  | zero =>
    intro S v w hk hSY hsupp hlen
    have hempty : Y \ S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hk)
    have hYS : Y ⊆ S := by
      intro z hz
      by_contra hzS
      exact absurd (Finset.mem_sdiff.mpr ⟨hz, hzS⟩) (by simp [hempty])
    have hSeq : S = Y := Finset.Subset.antisymm hSY hYS
    subst hSeq
    exact ⟨w, hsupp, hlen⟩
  | succ k ih =>
    intro S v w hk hSY hsupp hlen
    by_cases hSY' : S = Y
    · subst hSY'; exact ⟨w, hsupp, hlen⟩
    · have hne : S.Nonempty := ⟨v, by rw [← hsupp]; simp⟩
      obtain ⟨x, hxS, y, hyY, hyS, hxy⟩ := hconn S hSY hne hSY'
      have hx : x ∈ w.support := by rw [← List.mem_toFinset, hsupp]; exact hxS
      obtain ⟨w', hw's, hw'l⟩ := exists_detour w hx hxy
      refine ih (insert y S) v w' ?_ (Finset.insert_subset hyY hSY) ?_ ?_
      · have hsd : Y \ insert y S = (Y \ S).erase y := by
          ext z; simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]; tauto
        rw [hsd]
        have hmem : y ∈ Y \ S := Finset.mem_sdiff.mpr ⟨hyY, hyS⟩
        have := Finset.card_erase_of_mem hmem
        omega
      · rw [hw's, hsupp]
      · rw [hw'l, Finset.card_insert_of_notMem hyS]; omega

/-- **Closed tour of a connected domain.**  A domain-connected finite set `Y`
containing `v` carries a closed walk based at `v` whose support is exactly `Y` and
whose length is at most `2 (#Y - 1)`. -/
theorem exists_closed_tour {Y : Finset V} (hconn : IsDomainConnected G Y) {v : V}
    (hv : v ∈ Y) :
    ∃ w : G.Walk v v, w.support.toFinset = Y ∧ w.length + 2 ≤ 2 * #Y := by
  refine exists_tour_of_subset Y hconn #(Y \ {v}) {v} v Walk.nil le_rfl
    (Finset.singleton_subset_iff.mpr hv) (by simp) ?_
  simp

/-- Every vertex of a domain-connected set is joined to the base point by a walk that
stays inside the set. -/
theorem reachable_within_of_isDomainConnected {Y : Finset V} (hconn : IsDomainConnected G Y)
    {v : V} (hv : v ∈ Y) {z : V} (hz : z ∈ Y) :
    ∃ p : G.Walk v z, ∀ u ∈ p.support, u ∈ Y := by
  obtain ⟨w, hws, _⟩ := exists_closed_tour hconn hv
  have hzw : z ∈ w.support := by rw [← List.mem_toFinset, hws]; exact hz
  refine ⟨w.takeUntil z hzw, fun u hu => ?_⟩
  have hsub := Walk.support_takeUntil_subset w hzw hu
  rw [← hws]
  exact List.mem_toFinset.mpr hsub

/-- A walk that starts inside `S`, ends outside `S` and stays in `Y` must use an edge
of `G` leaving `S` inside `Y`. -/
theorem exists_boundary_edge_of_walk {S Y : Finset V} {u z : V} (p : G.Walk u z)
    (hz : z ∉ S) :
    (∀ c ∈ p.support, c ∈ Y) → u ∈ S → ∃ x ∈ S, ∃ y ∈ Y, y ∉ S ∧ G.Adj x y := by
  induction p with
  | nil => intro _ hu; exact absurd hu hz
  | cons hadj q ih =>
    rename_i a b _
    intro hsub ha
    by_cases hbS : b ∈ S
    · exact ih hz (fun c hc => hsub c (by simp [hc])) hbS
    · exact ⟨a, ha, b, hsub b (by simp), hbS, hadj⟩

/-- Conversely, a set in which every vertex is reachable from the base point through
the set is domain connected.  Together with `reachable_within_of_isDomainConnected`
this identifies `IsDomainConnected` with ordinary connectedness inside `Y`. -/
theorem isDomainConnected_of_reachable_within {Y : Finset V} {v : V}
    (h : ∀ z ∈ Y, ∃ p : G.Walk v z, ∀ u ∈ p.support, u ∈ Y) :
    IsDomainConnected G Y := by
  intro S hSY hSne hSneY
  obtain ⟨s, hs⟩ := hSne
  obtain ⟨z, hzY, hzS⟩ : ∃ z ∈ Y, z ∉ S := by
    by_contra hcon
    push_neg at hcon
    exact hSneY (Finset.Subset.antisymm hSY fun y hy => hcon y hy)
  obtain ⟨p₁, hp₁⟩ := h s (hSY hs)
  obtain ⟨p₂, hp₂⟩ := h z hzY
  refine exists_boundary_edge_of_walk (p₁.reverse.append p₂) hzS (fun u hu => ?_) hs
  rcases Walk.mem_support_append_iff .. |>.mp hu with hu | hu
  · exact hp₁ u (by simpa using hu)
  · exact hp₂ u hu

/-- The support of a walk is a domain-connected set.  Hence the localization domains
produced by the expansion (supports of connecting trees) automatically satisfy the
hypothesis of the counting theorem. -/
theorem isDomainConnected_support {a b : V} (w : G.Walk a b) :
    IsDomainConnected G w.support.toFinset := by
  refine isDomainConnected_of_reachable_within (v := a) fun z hz => ?_
  have hzw : z ∈ w.support := List.mem_toFinset.mp hz
  exact ⟨w.takeUntil z hzw, fun u hu =>
    List.mem_toFinset.mpr (Walk.support_takeUntil_subset w hzw hu)⟩

end RequestProject.YangMills.Cluster
