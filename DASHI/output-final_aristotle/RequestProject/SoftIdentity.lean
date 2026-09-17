/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Engine

/-!
# Soft identity: `said to be the same as` (P460) and `different from` (P1889)

Wikidata records two opposite *soft* judgements about identity of items:

* **said to be the same as** (P460): the two items may denote the same thing —
  the statement is a claim about the sources, not a merge;
* **different from** (P1889): the two items are explicitly *not* the same, most
  often to keep easily confused items apart.

Neither is a logical identity: P460 is symmetric but is not asserted transitively,
while an editor who follows a chain of P460 statements is implicitly taking its
transitive closure.  This file makes that closure explicit and shows what can go
wrong with it.

* `Wikidata.IdentityLayer` — the two statement lists, with `IdentityLayer.Same`,
  the reflexive–symmetric–transitive closure of P460, and `IdentityLayer.Diff`,
  the symmetric reading of P1889.  Proved: `Same` is an equivalence relation
  containing every declared P460 statement, and it is the *smallest* one
  (`same_le_of_equivalence`), so following P460 chains commits one to exactly this
  relation and no more.
* `IdentityLayer.sameSet` / `sameB` — the certified decision procedure for `Same`,
  built from the saturation engine of `RequestProject.Reachability`.
* `IdentityLayer.Conflict` — a pair that the closure identifies although P1889
  declares them different, with the decidable check `conflictB` proved to detect
  exactly the conflicts.
* `IdentityLayer.MergeSafe` — the interaction with the class layer: two items
  that the closure identifies must not be instances of classes declared disjoint.
  The executable check `mergeSafeB` is proved sound for this.

The worked fragment has three items linked by two P460 statements and a P1889
statement between the two ends: each individual statement is unobjectionable, yet
the closure conflicts — and a second fragment shows the closure identifying an
instance of `human` with an instance of the disjoint class `city`, which the
merge-safety check rejects.
-/

namespace Wikidata

/-- The soft identity layer of an ontology: the `said to be the same as` (P460)
and `different from` (P1889) statements. -/
structure IdentityLayer where
  /-- `said to be the same as` (P460) statements. -/
  same : List (Qid × Qid) := []
  /-- `different from` (P1889) statements. -/
  diff : List (Qid × Qid) := []
deriving DecidableEq, Repr, Inhabited

namespace IdentityLayer

variable (L : IdentityLayer)

/-- One step of the identity closure: a P460 statement read in either direction. -/
def SameStep (x y : Qid) : Prop := (x, y) ∈ L.same ∨ (y, x) ∈ L.same

/-- The identity closure of the P460 statements. -/
def Same : Qid → Qid → Prop := Relation.ReflTransGen L.SameStep

/-- The symmetric reading of the P1889 statements. -/
def Diff (x y : Qid) : Prop := (x, y) ∈ L.diff ∨ (y, x) ∈ L.diff

theorem sameStep_symm {x y : Qid} (h : L.SameStep x y) : L.SameStep y x := h.symm

theorem same_refl (x : Qid) : L.Same x x := Relation.ReflTransGen.refl

theorem same_of_step {x y : Qid} (h : L.SameStep x y) : L.Same x y :=
  Relation.ReflTransGen.single h

/-- A declared P460 statement identifies its two items. -/
theorem same_of_declared {x y : Qid} (h : (x, y) ∈ L.same) : L.Same x y :=
  L.same_of_step (Or.inl h)

theorem same_trans {x y z : Qid} (h : L.Same x y) (h' : L.Same y z) : L.Same x z := h.trans h'

theorem same_symm {x y : Qid} (h : L.Same x y) : L.Same y x :=
  Relation.ReflTransGen.symmetric (fun _ _ => L.sameStep_symm) h

/-- The identity closure is an equivalence relation. -/
theorem same_equivalence : Equivalence L.Same :=
  ⟨L.same_refl, fun h => L.same_symm h, fun h h' => L.same_trans h h'⟩

/-- It is the *smallest* equivalence relation containing the declared statements:
committing to P460 chains commits to exactly this relation. -/
theorem same_le_of_equivalence {R : Qid → Qid → Prop} (hR : Equivalence R)
    (hcontains : ∀ x y, (x, y) ∈ L.same → R x y) {x y : Qid} (h : L.Same x y) : R x y := by
  induction h with
  | refl => exact hR.refl x
  | tail _ hstep ih =>
      rcases hstep with hs | hs
      · exact hR.trans ih (hcontains _ _ hs)
      · exact hR.trans ih (hR.symm (hcontains _ _ hs))

theorem diff_symm {x y : Qid} (h : L.Diff x y) : L.Diff y x := h.symm

/-! ### Deciding the identity closure -/

/-- All items mentioned in the P460 statements. -/
def allF : Finset Qid := (L.same.map Prod.fst ++ L.same.map Prod.snd).toFinset

/-- The items directly linked to `q` by a P460 statement, in either direction. -/
def neighbours (q : Qid) : Finset Qid :=
  ((L.same.filter (fun p => decide (p.1 = q))).map Prod.snd).toFinset ∪
    ((L.same.filter (fun p => decide (p.2 = q))).map Prod.fst).toFinset

theorem mem_neighbours {q v : Qid} : v ∈ L.neighbours q ↔ L.SameStep q v := by
  simp only [neighbours, Finset.mem_union, List.mem_toFinset, List.mem_map, List.mem_filter,
    decide_eq_true_eq, SameStep]
  constructor
  · rintro (⟨⟨a, b⟩, ⟨hp, h1⟩, h2⟩ | ⟨⟨a, b⟩, ⟨hp, h1⟩, h2⟩) <;> simp only at h1 h2 <;>
      subst h1 <;> subst h2
    · exact Or.inl hp
    · exact Or.inr hp
  · rintro (h | h)
    · exact Or.inl ⟨(q, v), ⟨h, rfl⟩, rfl⟩
    · exact Or.inr ⟨(v, q), ⟨h, rfl⟩, rfl⟩

theorem neighbours_subset_allF (q : Qid) : L.neighbours q ⊆ L.allF := by
  intro v hv
  have h := L.mem_neighbours.1 hv
  simp only [allF, List.mem_toFinset, List.mem_append, List.mem_map]
  rcases h with h | h
  · exact Or.inr ⟨(q, v), h, rfl⟩
  · exact Or.inl ⟨(v, q), h, rfl⟩

theorem neighbours_eq_empty {q : Qid} (h : q ∉ L.allF) : L.neighbours q = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 (fun v hv => h ?_)
  have hw := L.mem_neighbours.1 hv
  simp only [allF, List.mem_toFinset, List.mem_append, List.mem_map]
  rcases hw with hw | hw
  · exact Or.inl ⟨(q, v), hw, rfl⟩
  · exact Or.inr ⟨(v, q), hw, rfl⟩

/-- The computed identity class of an item. -/
def sameSet (q : Qid) : Finset Qid := Reach.reach L.neighbours L.allF q

/-- The decision procedure for the identity closure. -/
def sameB (x y : Qid) : Bool := decide (y ∈ L.sameSet x)

/-- The computation decides the closure exactly. -/
theorem mem_sameSet_iff (x y : Qid) : y ∈ L.sameSet x ↔ L.Same x y := by
  rw [sameSet,
    Reach.mem_reach_iff_of_closed L.neighbours L.neighbours_subset_allF
      (fun _ hy => L.neighbours_eq_empty hy)]
  constructor
  · exact fun h => h.mono (fun _ _ hab => L.mem_neighbours.1 hab)
  · exact fun h => h.mono (fun _ _ hab => L.mem_neighbours.2 hab)

@[simp] theorem sameB_iff (x y : Qid) : L.sameB x y = true ↔ L.Same x y := by
  rw [sameB, decide_eq_true_iff, mem_sameSet_iff]

theorem sameB_symm {x y : Qid} (h : L.sameB x y = true) : L.sameB y x = true :=
  (L.sameB_iff y x).2 (L.same_symm ((L.sameB_iff x y).1 h))

/-! ### Identity conflicts -/

/-- A **conflict**: two items the P460 closure identifies although P1889 declares
them different. -/
def Conflict : Prop := ∃ x y : Qid, L.Same x y ∧ L.Diff x y

/-- The decidable conflict check. -/
def conflictB : Bool := L.diff.any (fun p => L.sameB p.1 p.2)

/-- The check detects exactly the conflicts. -/
theorem conflictB_iff : L.conflictB = true ↔ L.Conflict := by
  simp only [conflictB, List.any_eq_true]
  constructor
  · rintro ⟨⟨x, y⟩, hmem, hsame⟩
    exact ⟨x, y, (L.sameB_iff x y).1 hsame, Or.inl hmem⟩
  · rintro ⟨x, y, hsame, hdiff | hdiff⟩
    · exact ⟨(x, y), hdiff, (L.sameB_iff x y).2 hsame⟩
    · exact ⟨(y, x), hdiff, (L.sameB_iff y x).2 (L.same_symm hsame)⟩

/-- A layer whose P460 statements never link items declared different has no
conflict. -/
theorem not_conflict_of_diff_nil (h : L.diff = []) : ¬ L.Conflict := by
  rw [← conflictB_iff, conflictB, h]
  simp

/-! ### Interaction with the class layer -/

variable (kb : KB)

/-- Merging along the identity closure is *safe* for a knowledge base when no two
identified items are instances of classes declared disjoint. -/
def MergeSafe (kb : KB) (L : IdentityLayer) : Prop :=
  ∀ ⦃x y c d : Qid⦄, x ∈ kb.items → y ∈ kb.items → L.Same x y → kb.Disj c d →
    kb.isInstanceOf x c = true → kb.isInstanceOf y d = true → False

/-- The executable merge-safety check over the items of the base. -/
def mergeSafeB (kb : KB) (L : IdentityLayer) : Bool :=
  kb.items.all (fun x => kb.items.all (fun y => !L.sameB x y ||
    kb.disj.all (fun cd => !(kb.isInstanceOf x cd.1 && kb.isInstanceOf y cd.2) &&
      !(kb.isInstanceOf x cd.2 && kb.isInstanceOf y cd.1))))

/-- Soundness of the check: if it passes, no two identified items of the base are
instances of disjoint classes. -/
theorem mergeSafe_of_mergeSafeB (h : mergeSafeB kb L = true) : MergeSafe kb L := by
  intro x y c d hx hy hsame hdisj hxc hyd
  simp only [mergeSafeB, List.all_eq_true] at h
  have hrow := h x hx y hy
  rw [(L.sameB_iff x y).2 hsame] at hrow
  simp only [Bool.not_true, Bool.false_or, List.all_eq_true] at hrow
  rcases (show (c, d) ∈ kb.disj ∨ (d, c) ∈ kb.disj from hdisj) with hd | hd
  · have := hrow (c, d) hd
    simp [hxc, hyd] at this
  · have := hrow (d, c) hd
    simp [hxc, hyd] at this

end IdentityLayer

/-! ### A worked fragment: a chain of P460 statements that conflicts -/

namespace SoftIdentityExample

open Wikidata

/-- The first of three items said to be the same. -/
def a : Qid := .wd "Q1"
/-- The middle item. -/
def b : Qid := .wd "Q2"
/-- The third item, declared different from the first. -/
def c : Qid := .wd "Q3"

/-- Two P460 statements and one P1889 statement: each is unobjectionable on its
own. -/
def chain : IdentityLayer where
  same := [(a, b), (b, c)]
  diff := [(a, c)]

/-- The closure identifies the two ends of the chain … -/
theorem chain_same : chain.Same a c := (chain.sameB_iff a c).1 (by decide)

/-- … although they are declared different, so the layer conflicts. -/
theorem chain_conflict : chain.Conflict := chain.conflictB_iff.1 (by decide)

/-- Dropping the middle statement removes the conflict: the two ends are then
unrelated. -/
def broken : IdentityLayer := { chain with same := [(a, b)] }

theorem broken_not_same : ¬ broken.Same a c := by
  rw [← IdentityLayer.sameB_iff]
  decide

theorem broken_no_conflict : ¬ broken.Conflict := by
  rw [← IdentityLayer.conflictB_iff]
  decide

/-! #### Identifying instances of disjoint classes -/

/-- *human* (Q5). -/
def human : Qid := .wd "Q5"
/-- *city* (Q515). -/
def city : Qid := .wd "Q515"
/-- An instance of `human`. -/
def someone : Qid := .wd "Q42"
/-- An instance of `city`. -/
def somewhere : Qid := .wd "Q64"

/-- A small valid base with two disjoint classes. -/
def base : KB where
  name := "identity example"
  items := [human, city, someone, somewhere]
  levels := [(human, 1), (city, 1), (someone, 0), (somewhere, 0)]
  inst := [(someone, human), (somewhere, city)]
  disj := [(human, city)]

theorem base_valid : base.valid = true := by decide

/-- Nothing is identified, so merging is safe. -/
def noLinks : IdentityLayer := {}

theorem noLinks_safe : IdentityLayer.mergeSafeB base noLinks = true := by decide

/-- Saying that the person and the city are the same is rejected by the
merge-safety check. -/
def badLink : IdentityLayer := { same := [(someone, somewhere)] }

theorem badLink_unsafe : IdentityLayer.mergeSafeB base badLink = false := by decide

/-- The two items really are identified by the closure. -/
theorem badLink_same : badLink.Same someone somewhere :=
  (badLink.sameB_iff someone somewhere).1 (by decide)

end SoftIdentityExample

end Wikidata
