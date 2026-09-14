import RequestProject.CenterRetractionMore

/-!
# Symmetric and alternating groups retract onto their center

This file adds two more families to the study of groups retracting onto their center
(`HasCenterRetraction`, see `RequestProject.CenterRetraction`).

* `center_perm_eq_bot` : the symmetric group on a type with at least three elements is
  centerless. (Proved here from scratch: conjugating by a transposition moves any
  non-identity permutation.)
* `hasCenterRetraction_perm` : hence every symmetric group `Equiv.Perm α` on a finite type
  retracts onto its center — for `3 ≤ #α` because the center is trivial, for `#α ≤ 2`
  because the group is abelian. `hasCenterRetraction_perm_fin` is the statement for `Sₙ`.
* `hasCenterRetraction_alternatingGroup` : likewise every alternating group retracts onto its
  center; for `4 ≤ #α` this uses Mathlib's computation of the center of `Aₙ`.

Together with `RequestProject.CenterRetractionMore` this file also records a general negative
criterion, `not_hasCenterRetraction_of_center_le_commutator`: a group whose nontrivial center
lies inside its derived subgroup never retracts onto its center.
-/

open Subgroup

namespace CenterRetractionPerm

/-! ### Two small-order commutativity facts -/

/-- A group with at most two elements is commutative. -/
theorem commute_of_card_le_two {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 2) (a b : G) :
    a * b = b * a := by
  classical
  have := Fintype.ofFinite G
  rcases eq_or_ne a 1 with rfl | ha
  · simp
  rcases eq_or_ne b 1 with rfl | hb
  · simp
  have hab : a = b := by
    by_contra hne
    have hsub : ({1, a, b} : Finset G) ⊆ Finset.univ := Finset.subset_univ _
    have hcard : ({1, a, b} : Finset G).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha, Ne.symm hb]),
        Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
    have h3 := Finset.card_le_card hsub
    rw [hcard, Finset.card_univ, ← Nat.card_eq_fintype_card] at h3
    omega
  rw [hab]

/-- A group with at most three elements is commutative (it is trivial, or of prime order). -/
theorem commute_of_card_le_three {G : Type*} [Group G] [Finite G] (h : Nat.card G ≤ 3) (a b : G) :
    a * b = b * a := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  interval_cases hc : Nat.card G
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.1 hc).1
    exact Subsingleton.elim _ _
  · exact commute_of_card_le_two (by omega) a b
  · have : IsCyclic G := isCyclic_of_prime_card hc
    letI := IsCyclic.commGroup (α := G)
    exact mul_comm a b

/-! ### Symmetric groups -/

variable {α : Type*} [DecidableEq α]

/-- **Symmetric groups on at least three letters are centerless.** -/
theorem center_perm_eq_bot [Fintype α] (hα : 3 ≤ Fintype.card α) :
    center (Equiv.Perm α) = ⊥ := by
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ a := by
    by_contra h
    push_neg at h
    exact hne (Equiv.ext h)
  set b := σ a with hb
  -- pick a third point `c ∉ {a, b}`
  obtain ⟨c, hc⟩ : ∃ c : α, c ∉ ({a, b} : Finset α) := by
    have hcard : ({a, b} : Finset α).card < (Finset.univ : Finset α).card := by
      have h2 : ({a, b} : Finset α).card ≤ 2 := by
        simpa using (Finset.card_insert_le a {b}).trans (by simp)
      simpa [Finset.card_univ] using lt_of_le_of_lt h2 (by omega : 2 < Fintype.card α)
    obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    exact ⟨c, hc⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨hca, hcb⟩ := hc
  -- centrality applied to the transposition `swap b c`
  have hcomm : σ * Equiv.swap b c = Equiv.swap b c * σ := (mem_center_iff.1 hσ _).symm
  have h1 : (σ * Equiv.swap b c) a = b := by
    simp [Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hca), ← hb]
  have h2 : (Equiv.swap b c * σ) a = c := by
    simp [← hb, Equiv.swap_apply_left]
  rw [hcomm, h2] at h1
  exact hcb h1

/-- **Every symmetric group on a finite type retracts onto its center.** For at least three
letters the center is trivial; for fewer letters the group is abelian. -/
theorem hasCenterRetraction_perm [Fintype α] : HasCenterRetraction (Equiv.Perm α) := by
  rcases le_or_gt 3 (Fintype.card α) with hα | hα
  · exact hasCenterRetraction_of_center_eq_bot (center_perm_eq_bot hα)
  · refine hasCenterRetraction_of_commute (commute_of_card_le_two ?_)
    have hc : Nat.card (Equiv.Perm α) = Nat.factorial (Fintype.card α) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    rw [hc]
    interval_cases h : Fintype.card α <;> simp [Nat.factorial]

/-- The symmetric group `Sₙ` retracts onto its center, for every `n`. -/
theorem hasCenterRetraction_perm_fin (n : ℕ) : HasCenterRetraction (Equiv.Perm (Fin n)) :=
  hasCenterRetraction_perm

/-! ### Alternating groups -/

/-- **Every alternating group on a finite type retracts onto its center.** For at least four
letters the center is trivial; for fewer the group has order at most three, hence is abelian. -/
theorem hasCenterRetraction_alternatingGroup [Fintype α] :
    HasCenterRetraction (alternatingGroup α) := by
  rcases le_or_gt 4 (Nat.card α) with hα | hα
  · exact hasCenterRetraction_of_center_eq_bot (alternatingGroup.center_eq_bot hα)
  · rcases subsingleton_or_nontrivial α with hs | hn
    · haveI : Subsingleton (Equiv.Perm α) := inferInstance
      exact hasCenterRetraction_of_commute fun a b => Subtype.ext (Subsingleton.elim _ _)
    · refine hasCenterRetraction_of_commute (commute_of_card_le_three ?_)
      have h2 := two_mul_card_alternatingGroup (α := α)
      rw [Fintype.card_perm] at h2
      rw [Nat.card_eq_fintype_card] at hα
      have hf : Nat.factorial (Fintype.card α) ≤ 6 := by
        interval_cases h : Fintype.card α <;> simp [Nat.factorial]
      rw [Nat.card_eq_fintype_card]
      omega

/-- The alternating group `Aₙ` retracts onto its center, for every `n`. -/
theorem hasCenterRetraction_alternatingGroup_fin (n : ℕ) :
    HasCenterRetraction (alternatingGroup (Fin n)) :=
  hasCenterRetraction_alternatingGroup

end CenterRetractionPerm

/-! ### A general negative criterion -/

/-- A group whose center is nontrivial and contained in its derived subgroup does not retract
onto its center. -/
theorem not_hasCenterRetraction_of_center_le_commutator {G : Type*} [Group G]
    (hle : center G ≤ commutator G) (hne : center G ≠ ⊥) : ¬ HasCenterRetraction G := by
  rintro ⟨r, hr⟩
  refine hne (le_bot_iff.1 ?_)
  have hdisj := disjoint_commutator_center (r := r) hr
  exact le_of_eq_of_le (inf_eq_right.2 hle).symm hdisj.le_bot

