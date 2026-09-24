import Mathlib

/-!
# Executable reachability in a finite graph

This module provides a *computable* reachability procedure for a graph given by a
successor function `succ : Q → Finset Q` whose values live inside a finite ambient
set `all : Finset Q`, together with soundness and completeness theorems relating it
to `Relation.ReflTransGen`.

It is the computational engine used by the Wikidata ontology model: the `subclass of`
(P279) and `instance of` (P31) closures are computed with `Reach.reach`.
-/

namespace Reach

variable {Q : Type*} [DecidableEq Q]

/-- One step of saturation: add all successors of the current set. -/
def step (succ : Q → Finset Q) (S : Finset Q) : Finset Q :=
  S ∪ S.biUnion succ

/-- The `n`-fold saturation of `{x}`. -/
def iter (succ : Q → Finset Q) (n : ℕ) (x : Q) : Finset Q :=
  (step succ)^[n] {x}

theorem subset_step (succ : Q → Finset Q) (S : Finset Q) : S ⊆ step succ S := by
  intro a ha; exact Finset.mem_union_left _ ha

theorem step_mono (succ : Q → Finset Q) {S T : Finset Q} (h : S ⊆ T) :
    step succ S ⊆ step succ T := by
  intro a ha
  rcases Finset.mem_union.1 ha with ha | ha
  · exact Finset.mem_union_left _ (h ha)
  · rcases Finset.mem_biUnion.1 ha with ⟨b, hb, hab⟩
    exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨b, h hb, hab⟩)

theorem iter_succ (succ : Q → Finset Q) (n : ℕ) (x : Q) :
    iter succ (n + 1) x = step succ (iter succ n x) := by
  simp [iter, Function.iterate_succ_apply']

theorem iter_zero (succ : Q → Finset Q) (x : Q) : iter succ 0 x = {x} := rfl

theorem iter_subset_succ (succ : Q → Finset Q) (n : ℕ) (x : Q) :
    iter succ n x ⊆ iter succ (n + 1) x := by
  rw [iter_succ]; exact subset_step _ _

theorem iter_mono (succ : Q → Finset Q) {m n : ℕ} (h : m ≤ n) (x : Q) :
    iter succ m x ⊆ iter succ n x := by
  induction n with
  | zero => simp [Nat.le_zero.1 h]
  | succ k ih =>
      rcases Nat.lt_or_ge m (k + 1) with hk | hk
      · exact (ih (Nat.lt_succ_iff.1 hk)).trans (iter_subset_succ succ k x)
      · have : m = k + 1 := le_antisymm h hk
        subst this; exact Finset.Subset.refl _

/-- If saturation does not grow at step `n`, it never grows again. -/
theorem iter_stable (succ : Q → Finset Q) {n : ℕ} {x : Q}
    (h : iter succ (n + 1) x = iter succ n x) :
    ∀ m, iter succ (n + m) x = iter succ n x := by
  intro m
  induction m with
  | zero => rfl
  | succ k ih =>
      have : n + (k + 1) = (n + k) + 1 := by ring
      rw [this, iter_succ, ih, ← iter_succ, h]

theorem iter_subset_all (succ : Q → Finset Q) {all : Finset Q}
    (hsucc : ∀ y, succ y ⊆ all) {x : Q} (hx : x ∈ all) (n : ℕ) :
    iter succ n x ⊆ all := by
  induction n with
  | zero => simpa [iter_zero] using hx
  | succ k ih =>
      rw [iter_succ]
      intro a ha
      rcases Finset.mem_union.1 ha with ha | ha
      · exact ih ha
      · rcases Finset.mem_biUnion.1 ha with ⟨b, _, hab⟩
        exact hsucc b hab

/-- Saturation stabilises after at most `all.card` steps. -/
theorem exists_stable (succ : Q → Finset Q) {all : Finset Q}
    (hsucc : ∀ y, succ y ⊆ all) {x : Q} (hx : x ∈ all) :
    ∃ n ≤ all.card, iter succ (n + 1) x = iter succ n x := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ n ≤ all.card, n + 1 ≤ (iter succ n x).card := by
    intro n hn
    induction n with
    | zero => simp [iter_zero]
    | succ k ih =>
        have hk : k ≤ all.card := Nat.le_of_succ_le hn
        have hlt : (iter succ k x).card < (iter succ (k + 1) x).card := by
          refine Finset.card_lt_card ?_
          exact HasSubset.Subset.ssubset_of_ne (iter_subset_succ succ k x)
            (fun h => hcon k hk h.symm)
        exact Nat.succ_le_of_lt (lt_of_le_of_lt (ih hk) hlt)
  have h1 : all.card + 1 ≤ (iter succ all.card x).card := key all.card le_rfl
  have h2 : (iter succ all.card x).card ≤ all.card :=
    Finset.card_le_card (iter_subset_all succ hsucc hx all.card)
  omega

/-- The computed reachable set: saturate `all.card` times. -/
def reach (succ : Q → Finset Q) (all : Finset Q) (x : Q) : Finset Q :=
  iter succ all.card x

theorem mem_reach_self (succ : Q → Finset Q) (all : Finset Q) (x : Q) :
    x ∈ reach succ all x := by
  have : ({x} : Finset Q) ⊆ iter succ all.card x := by
    simpa [iter_zero] using iter_mono succ (Nat.zero_le all.card) x
  exact this (Finset.mem_singleton_self x)

/-- Soundness: everything computed is genuinely reachable. -/
theorem reflTransGen_of_mem_iter (succ : Q → Finset Q) (n : ℕ) (x b : Q)
    (h : b ∈ iter succ n x) :
    Relation.ReflTransGen (fun u v => v ∈ succ u) x b := by
  induction n generalizing b with
  | zero =>
      rw [iter_zero, Finset.mem_singleton] at h
      subst h; exact Relation.ReflTransGen.refl
  | succ k ih =>
      rw [iter_succ] at h
      rcases Finset.mem_union.1 h with h | h
      · exact ih b h
      · rcases Finset.mem_biUnion.1 h with ⟨c, hc, hcb⟩
        exact (ih c hc).tail hcb

/-- Completeness at some finite stage. -/
theorem exists_mem_iter_of_reflTransGen (succ : Q → Finset Q) {x b : Q}
    (h : Relation.ReflTransGen (fun u v => v ∈ succ u) x b) :
    ∃ n, b ∈ iter succ n x := by
  induction h with
  | refl => exact ⟨0, by simp [iter_zero]⟩
  | tail hab hbc ih =>
      rcases ih with ⟨n, hn⟩
      refine ⟨n + 1, ?_⟩
      rw [iter_succ]
      exact Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨_, hn, hbc⟩)

/-- The computation is a decision procedure for reachability. -/
theorem mem_reach_iff (succ : Q → Finset Q) {all : Finset Q}
    (hsucc : ∀ y, succ y ⊆ all) {x : Q} (hx : x ∈ all) (b : Q) :
    b ∈ reach succ all x ↔ Relation.ReflTransGen (fun u v => v ∈ succ u) x b := by
  constructor
  · intro h; exact reflTransGen_of_mem_iter succ _ x b h
  · intro h
    rcases exists_mem_iter_of_reflTransGen succ h with ⟨n, hn⟩
    rcases exists_stable succ hsucc hx with ⟨m, hm, hstab⟩
    have hall : ∀ k, iter succ (m + k) x = iter succ m x := iter_stable succ hstab
    rcases Nat.le_total n m with hnm | hnm
    · exact iter_mono succ hm x (iter_mono succ hnm x hn)
    · have : iter succ n x = iter succ m x := by
        have := hall (n - m)
        rwa [Nat.add_sub_cancel' hnm] at this
      rw [this] at hn
      exact iter_mono succ hm x hn

/-- A vertex with no successors reaches only itself. -/
theorem reach_eq_singleton_of_succ_empty (succ : Q → Finset Q) (all : Finset Q) {x : Q}
    (h : succ x = ∅) : reach succ all x = {x} := by
  have key : ∀ n, iter succ n x = {x} := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih => rw [iter_succ, ih]; simp [step, h]
  simpa [reach] using key _

/-- The decision procedure for reachability, without assuming that the source lies in
the ambient set: it is enough that vertices outside it have no successors. -/
theorem mem_reach_iff_of_closed (succ : Q → Finset Q) {all : Finset Q}
    (hsucc : ∀ y, succ y ⊆ all) (hout : ∀ y, y ∉ all → succ y = ∅) (x b : Q) :
    b ∈ reach succ all x ↔ Relation.ReflTransGen (fun u v => v ∈ succ u) x b := by
  by_cases hx : x ∈ all
  · exact mem_reach_iff succ hsucc hx b
  · rw [reach_eq_singleton_of_succ_empty succ all (hout x hx), Finset.mem_singleton]
    constructor
    · rintro rfl; exact Relation.ReflTransGen.refl
    · intro h
      rcases Relation.reflTransGen_iff_eq_or_transGen.1 h with h | h
      · exact h
      · obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.1 h
        simp [hout x hx] at hc

end Reach
