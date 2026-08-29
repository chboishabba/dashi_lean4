import RequestProject.Engine

/-!
# The kinship layer: `father` (P22), `mother` (P25) and `spouse` (P26)

*Wikidata:WikiProject Ontology* separates the class hierarchy from the many
*individual-level* relations that Wikidata records between people.  Genealogy is the
most familiar of them: `father` (P22) and `mother` (P25) relate an individual to
another individual, never a class to a class, and the resulting ancestry relation is
a hierarchy of its own — one that must not be confused with `subclass of` (P279) or
with the taxonomic `parent taxon` (P171) hierarchy of `RequestProject.Taxa`.

This file adds that layer on top of the executable knowledge base of
`RequestProject.Engine`.  An `FKB` is a `KB` together with

* `father` (P22) statements `(child, father)`,
* `mother` (P25) statements `(child, mother)`, and
* `spouse` (P26) statements, which Wikidata treats as symmetric.

Everything is computable — `FKB.descendsFromB`, `FKB.isProperAncestorB`,
`FKB.childrenL`, `FKB.ancestorsL`, `FKB.spouseB`, `FKB.siblingB`, `FKB.fullSiblingB`,
`FKB.relatedB` — and certified: for a
well-formed layer `descendsFromB` decides the reflexive–transitive closure of the
asserted parenthood statements (`FKB.descendsFromB_iff`).

The main results are:

* ancestry is a **partial order** on a valid layer, so *proper* ancestry is a strict
  order (`FKB.properAncestor_trans`, `FKB.properAncestor_asymm`) and the genealogy is
  **well founded** (`FKB.properAncestor_wf`): nobody is their own ancestor along a
  chain of any length (`FKB.not_transGen_properAncestor_self`);
* a validated layer gives each person **at most two parents**
  (`FKB.card_parents_le_two`), one father and one mother, and the recorded father and
  mother are unique (`FKB.fatherOf?_eq_some_iff`, `FKB.motherOf?_eq_some_iff`);
* siblinghood is symmetric and irreflexive, and full siblinghood implies siblinghood
  (`FKB.sibling_symm`, `FKB.sibling_irrefl`, `FKB.fullSibling_sibling`);
* being related (having a common ancestor) is reflexive on the items and symmetric,
  and holds between a person and each of their ancestors (`FKB.relatedB_symm`);
* the listed children and ancestors of a person are exactly the right ones
  (`FKB.mem_childrenL_iff`, `FKB.mem_ancestorsL_iff`), and `spouse` is symmetric and,
  on a validated layer, irreflexive (`FKB.spouseB_symm`, `FKB.spouseB_irrefl`);
* relatedness is **not transitive** (`FKB.related_not_transitive`) and half siblings
  are siblings but not full siblings (`FKB.halfSiblings_not_full`), both decided on
  worked fragments;
* the genealogy is **not** the taxonomy: a validated layer never asserts a parenthood
  statement between items related by `subclass of` or `instance of`
  (`FKB.parent_not_subclass`, `FKB.parent_not_instance`), and parenthood is not
  inherited through `instance of` — a worked counterexample is decided
  (`FKB.parent_not_inherited`).
-/

namespace Wikidata

/-- A finite, executable **kinship layer** over a knowledge base: the `father` (P22),
`mother` (P25) and `spouse` (P26) statements. -/
structure FKB where
  /-- The underlying item ontology (taxonomy). -/
  base : KB
  /-- `father` (P22) statements, written `(child, father)`. -/
  fathers : List (Qid × Qid) := []
  /-- `mother` (P25) statements, written `(child, mother)`. -/
  mothers : List (Qid × Qid) := []
  /-- `spouse` (P26) statements; the relation is understood symmetrically. -/
  spouses : List (Qid × Qid) := []
deriving Repr, DecidableEq, Inhabited

namespace FKB

variable (f : FKB)

/-! ### The computational engine -/

/-- The recorded parents of a person: father first, then mother. -/
def parentsL (q : Qid) : List Qid :=
  ((f.fathers.filter (fun r => r.1 == q)).map Prod.snd) ++
    ((f.mothers.filter (fun r => r.1 == q)).map Prod.snd)

/-- The recorded parents of a person, as a `Finset`. -/
def parentsF (q : Qid) : Finset Qid := (f.parentsL q).toFinset

/-- All ancestors of a person (themselves included), computed by saturating the
parenthood graph. -/
def ancestorClosure (q : Qid) : Finset Qid := Reach.reach f.parentsF f.base.allF q

/-- Decides (reflexive) descent: `a` is `b`, or a child of a child of … of `b`. -/
def descendsFromB (a b : Qid) : Bool := b ∈ f.ancestorClosure a

/-- Decides *proper* ancestry: `b` is an ancestor of `a` other than `a` itself. -/
def isProperAncestorB (b a : Qid) : Bool := f.descendsFromB a b && a != b

/-- The recorded father of a person, if any. -/
def fatherOf? (q : Qid) : Option Qid := f.fathers.lookup q

/-- The recorded mother of a person, if any. -/
def motherOf? (q : Qid) : Option Qid := f.mothers.lookup q

/-- The recorded children of a person, among the items. -/
def childrenL (p : Qid) : List Qid := f.base.items.filter (fun c => p ∈ f.parentsL c)

/-- The ancestors of a person, among the items (themselves included). -/
def ancestorsL (a : Qid) : List Qid := f.base.items.filter (fun b => f.descendsFromB a b)

/-- Decides the `spouse` (P26) relation, which Wikidata treats symmetrically. -/
def spouseB (a b : Qid) : Bool := ((a, b) ∈ f.spouses) || ((b, a) ∈ f.spouses)

/-- Two people are **siblings** when they are distinct and share a parent. -/
def siblingB (a b : Qid) : Bool :=
  a != b && f.base.items.any (fun p => p ∈ f.parentsL a && p ∈ f.parentsL b)

/-- Two people are **full siblings** when they are distinct and have the same
recorded father and the same recorded mother, both present. -/
def fullSiblingB (a b : Qid) : Bool :=
  a != b &&
    (match f.fatherOf? a, f.fatherOf? b with
      | some x, some y => x == y
      | _, _ => false) &&
    (match f.motherOf? a, f.motherOf? b with
      | some x, some y => x == y
      | _, _ => false)

/-- The common ancestors of two people. -/
def commonAncestors (a b : Qid) : Finset Qid := f.ancestorClosure a ∩ f.ancestorClosure b

/-- Two people are **related** when they have a common ancestor. -/
def relatedB (a b : Qid) : Bool := ¬ (f.commonAncestors a b) = ∅

/-- The number of ancestors of a person (themselves included): the measure that makes
the genealogy well founded. -/
def generationHeight (a : Qid) : ℕ := (f.ancestorClosure a).card

/-! ### The validator -/

/-- All kinship statements mention declared items. -/
def fWellFormed : Bool :=
  f.base.wellFormed &&
  f.fathers.all (fun r => r.1 ∈ f.base.items && r.2 ∈ f.base.items) &&
  f.mothers.all (fun r => r.1 ∈ f.base.items && r.2 ∈ f.base.items) &&
  f.spouses.all (fun r => r.1 ∈ f.base.items && r.2 ∈ f.base.items)

/-- Nobody has two different fathers, and nobody has two different mothers. -/
def singleParents : Bool :=
  f.fathers.all (fun r => f.fathers.all (fun s => r.1 != s.1 || r.2 == s.2)) &&
  f.mothers.all (fun r => f.mothers.all (fun s => r.1 != s.1 || r.2 == s.2))

/-- The ancestry relation has no cycles. -/
def fAcyclic : Bool :=
  f.base.items.all (fun a => f.base.items.all
    (fun b => !(f.descendsFromB a b && f.descendsFromB b a) || a == b))

/-- Nobody is their own spouse. -/
def noSelfSpouse : Bool := f.spouses.all (fun r => r.1 != r.2)

/-- The genealogy is not the taxonomy: no asserted parenthood statement is also a
`subclass of` or an `instance of` fact. -/
def noKinClassConfusion : Bool :=
  (f.fathers ++ f.mothers).all
    (fun r => !f.base.isSubclassOf r.1 r.2 && !f.base.isInstanceOf r.1 r.2)

/-- The checks the kinship layer itself has to pass, over and above validity of the
underlying ontology. -/
def fLayerValid : Bool :=
  f.fWellFormed && f.singleParents && f.fAcyclic && f.noSelfSpouse && f.noKinClassConfusion

/-- The full validity check for a kinship layer. -/
def fValid : Bool := f.base.valid && f.fLayerValid

/-! ### Semantics -/

/-- The asserted `father` statements, as a relation. -/
def Father (c p : Qid) : Prop := (c, p) ∈ f.fathers

/-- The asserted `mother` statements, as a relation. -/
def Mother (c p : Qid) : Prop := (c, p) ∈ f.mothers

/-- The asserted parenthood statements, as a relation. -/
def Parent (c p : Qid) : Prop := f.Father c p ∨ f.Mother c p

/-- Derived descent: the reflexive–transitive closure of the parenthood statements. -/
def DescendsFrom (a b : Qid) : Prop := Relation.ReflTransGen f.Parent a b

variable {f}

theorem mem_parentsL {c p : Qid} : p ∈ f.parentsL c ↔ f.Parent c p := by
  simp [parentsL, Parent, Father, Mother, List.mem_filter, List.mem_map]

theorem mem_parentsF {c p : Qid} : p ∈ f.parentsF c ↔ f.Parent c p := by
  simpa [parentsF] using mem_parentsL

theorem succ_eq_parent (f : FKB) : (fun u v => v ∈ f.parentsF u) = f.Parent := by
  funext u v; exact propext mem_parentsF

theorem fwf_base (h : f.fWellFormed = true) : f.base.wellFormed = true := by
  simp only [fWellFormed, Bool.and_eq_true] at h; tauto

/-- Both endpoints of a parenthood statement of a well-formed layer are items. -/
theorem fwf_parent (h : f.fWellFormed = true) {c p : Qid} (hcp : f.Parent c p) :
    c ∈ f.base.items ∧ p ∈ f.base.items := by
  simp only [fWellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  rcases hcp with hcp | hcp
  · simpa using h.1.1.2 (c, p) hcp
  · simpa using h.1.2 (c, p) hcp

theorem parentsF_subset_allF (h : f.fWellFormed = true) (y : Qid) :
    f.parentsF y ⊆ f.base.allF := by
  intro p hp
  simpa [KB.allF] using (fwf_parent h (mem_parentsF.1 hp)).2

theorem parentsF_eq_empty_of_not_mem (h : f.fWellFormed = true) {a : Qid}
    (ha : a ∉ f.base.items) : f.parentsF a = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 fun p hp => ?_
  exact ha (fwf_parent h (mem_parentsF.1 hp)).1

/-- **Certified ancestry computation**: in a well-formed layer the Boolean check
`descendsFromB` decides the reflexive–transitive closure of the asserted P22/P25
statements. -/
theorem descendsFromB_iff (h : f.fWellFormed = true) (a b : Qid) :
    f.descendsFromB a b = true ↔ f.DescendsFrom a b := by
  have hcl := Reach.mem_reach_iff_of_closed f.parentsF (parentsF_subset_allF h)
    (fun y hy => parentsF_eq_empty_of_not_mem h (by simpa [KB.allF] using hy)) a b
  rw [succ_eq_parent] at hcl
  simpa [descendsFromB, ancestorClosure, DescendsFrom] using hcl

theorem descendsFromB_refl (f : FKB) (a : Qid) : f.descendsFromB a a = true := by
  simpa [descendsFromB, ancestorClosure] using Reach.mem_reach_self f.parentsF f.base.allF a

theorem descendsFromB_of_parent (h : f.fWellFormed = true) {c p : Qid} (hcp : f.Parent c p) :
    f.descendsFromB c p = true :=
  (descendsFromB_iff h c p).2 (Relation.ReflTransGen.single hcp)

theorem descendsFromB_trans (h : f.fWellFormed = true) {a b c : Qid}
    (hab : f.descendsFromB a b = true) (hbc : f.descendsFromB b c = true) :
    f.descendsFromB a c = true :=
  (descendsFromB_iff h a c).2 (((descendsFromB_iff h a b).1 hab).trans
    ((descendsFromB_iff h b c).1 hbc))

/-- Every ancestor of an item of the base is again an item of the base. -/
theorem mem_items_of_descendsFromB (h : f.fWellFormed = true) {a b : Qid}
    (ha : a ∈ f.base.items) (hab : f.descendsFromB a b = true) : b ∈ f.base.items := by
  have := (descendsFromB_iff h a b).1 hab
  induction this with
  | refl => exact ha
  | tail _ hstep _ => exact (fwf_parent h hstep).2

/-- Anyone with a proper ancestor is an item. -/
theorem mem_items_of_isProperAncestorB (h : f.fWellFormed = true) {a b : Qid}
    (hab : f.isProperAncestorB b a = true) : a ∈ f.base.items := by
  simp only [isProperAncestorB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab
  by_contra ha
  have hcl : f.DescendsFrom a b := (descendsFromB_iff h a b).1 hab.1
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hcl with rfl | hgen
  · exact hab.2 rfl
  · exact ha (fwf_parent h (Relation.TransGen.head'_iff.1 hgen).choose_spec.1).1

/-! ### Ancestry is a partial order, and the genealogy is well founded -/

/-- Antisymmetry of descent on a layer whose ancestry is acyclic. -/
theorem descendsFromB_antisymm (h : f.fWellFormed = true) (hac : f.fAcyclic = true) {a b : Qid}
    (hab : f.descendsFromB a b = true) (hba : f.descendsFromB b a = true) : a = b := by
  by_cases hne : a = b
  · exact hne
  · exfalso
    have ha : a ∈ f.base.items := mem_items_of_isProperAncestorB h (b := b) (by
      simp only [isProperAncestorB, Bool.and_eq_true, bne_iff_ne, ne_eq]
      exact ⟨hab, hne⟩)
    have hb : b ∈ f.base.items := mem_items_of_descendsFromB h ha hab
    simp only [fAcyclic, List.all_eq_true] at hac
    have := hac a ha b hb
    simp [hab, hba, hne] at this

theorem properAncestor_irrefl (f : FKB) (a : Qid) : f.isProperAncestorB a a = false := by
  simp [isProperAncestorB]

/-- Proper ancestry is asymmetric on a valid layer. -/
theorem properAncestor_asymm (h : f.fWellFormed = true) (hac : f.fAcyclic = true) {a b : Qid}
    (hab : f.isProperAncestorB a b = true) (hba : f.isProperAncestorB b a = true) : False := by
  simp only [isProperAncestorB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab hba
  exact hab.2 (descendsFromB_antisymm h hac hab.1 hba.1)

/-- Proper ancestry is transitive on a valid layer. -/
theorem properAncestor_trans (h : f.fWellFormed = true) (hac : f.fAcyclic = true) {a b c : Qid}
    (hab : f.isProperAncestorB a b = true) (hbc : f.isProperAncestorB b c = true) :
    f.isProperAncestorB a c = true := by
  simp only [isProperAncestorB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab hbc ⊢
  refine ⟨descendsFromB_trans h hbc.1 hab.1, ?_⟩
  rintro rfl
  exact hbc.2 (descendsFromB_antisymm h hac hbc.1 hab.1)

theorem ancestorClosure_subset (h : f.fWellFormed = true) {a b : Qid}
    (hab : f.descendsFromB a b = true) : f.ancestorClosure b ⊆ f.ancestorClosure a := by
  intro c hc
  have hbc : f.descendsFromB b c = true := by simpa [descendsFromB] using hc
  simpa [descendsFromB] using descendsFromB_trans h hab hbc

/-- **Each generation up strictly shrinks the ancestor set**: a person has strictly
more ancestors than any of their proper ancestors. -/
theorem generationHeight_lt (h : f.fWellFormed = true) (hac : f.fAcyclic = true) {a b : Qid}
    (hab : f.isProperAncestorB b a = true) : f.generationHeight b < f.generationHeight a := by
  have hab' : f.descendsFromB a b = true := by
    simp only [isProperAncestorB, Bool.and_eq_true] at hab
    exact hab.1
  refine Finset.card_lt_card ⟨ancestorClosure_subset h hab', fun hsub => ?_⟩
  have ha : a ∈ f.ancestorClosure a := by
    simpa [descendsFromB] using descendsFromB_refl f a
  have hba : f.descendsFromB b a = true := by simpa [descendsFromB] using hsub ha
  simp only [isProperAncestorB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab
  exact hab.2 (descendsFromB_antisymm h hac hab' hba)

/-- **The genealogy is well founded**: there is no infinite ascending chain of proper
ancestors, so one may reason by induction towards the ancestors. -/
theorem properAncestor_wf (h : f.fWellFormed = true) (hac : f.fAcyclic = true) :
    WellFounded (fun b a : Qid => f.isProperAncestorB b a = true) := by
  refine Subrelation.wf (r := InvImage (· < ·) f.generationHeight) ?_ (InvImage.wf _ Nat.lt_wfRel.wf)
  intro b a hab
  exact generationHeight_lt h hac hab

/-- Nobody is their own ancestor, even through a chain of parenthood statements. -/
theorem not_transGen_properAncestor_self (h : f.fWellFormed = true) (hac : f.fAcyclic = true)
    (a : Qid) : ¬ Relation.TransGen (fun x y : Qid => f.isProperAncestorB x y = true) a a := by
  intro hgen
  have key : ∀ {x y : Qid},
      Relation.TransGen (fun x y : Qid => f.isProperAncestorB x y = true) x y →
      f.isProperAncestorB x y = true := by
    intro x y hxy
    induction hxy with
    | single hstep => exact hstep
    | tail _ hstep ih => exact properAncestor_trans h hac ih hstep
  have := key hgen
  simp [properAncestor_irrefl] at this

/-! ### Fathers, mothers, and how many parents a person has -/

/-- A successful association-list lookup witnesses membership. -/
private theorem mem_of_lookup_some : ∀ {l : List (Qid × Qid)} {a b : Qid},
    l.lookup a = some b → (a, b) ∈ l := by
  intro l
  induction l with
  | nil => intro a b h; simp [List.lookup] at h
  | cons hd tl ih =>
    intro a b h
    rw [List.lookup] at h
    split at h
    · rename_i hh
      simp only [beq_iff_eq] at hh
      subst hh
      simp only [Option.some.injEq] at h
      subst h
      simp
    · exact List.mem_cons_of_mem _ (ih h)

/-- If a key occurs in an association list then the lookup succeeds. -/
private theorem lookup_some_of_mem : ∀ {l : List (Qid × Qid)} {a b : Qid},
    (a, b) ∈ l → ∃ c, l.lookup a = some c := by
  intro l
  induction l with
  | nil => intro a b h; simp at h
  | cons hd tl ih =>
    intro a b h
    rw [List.lookup]
    split
    · exact ⟨hd.2, rfl⟩
    · rename_i hh
      rcases List.mem_cons.1 h with h1 | h1
      · exfalso; rw [← h1] at hh; simp at hh
      · exact ih h1

/-- On a layer recording a single father per person, the lookup finds exactly the
asserted father. -/
theorem fatherOf?_eq_some_iff (hsp : f.singleParents = true) {c p : Qid} :
    f.fatherOf? c = some p ↔ f.Father c p := by
  constructor
  · intro hf
    exact mem_of_lookup_some (by simpa [fatherOf?] using hf)
  · intro hf
    simp only [singleParents, Bool.and_eq_true, List.all_eq_true] at hsp
    obtain ⟨q, hq⟩ : ∃ q, f.fatherOf? c = some q := lookup_some_of_mem hf
    have hq' : f.Father c q := mem_of_lookup_some (by simpa [fatherOf?] using hq)
    have := hsp.1 (c, q) hq' (c, p) hf
    simp only [bne_iff_ne, ne_eq, beq_iff_eq, Bool.or_eq_true] at this
    rcases this with h1 | h1
    · exact absurd trivial h1
    · rw [hq, h1]

/-- On a layer recording a single mother per person, the lookup finds exactly the
asserted mother. -/
theorem motherOf?_eq_some_iff (hsp : f.singleParents = true) {c p : Qid} :
    f.motherOf? c = some p ↔ f.Mother c p := by
  constructor
  · intro hf
    exact mem_of_lookup_some (by simpa [motherOf?] using hf)
  · intro hf
    simp only [singleParents, Bool.and_eq_true, List.all_eq_true] at hsp
    obtain ⟨q, hq⟩ : ∃ q, f.motherOf? c = some q := lookup_some_of_mem hf
    have hq' : f.Mother c q := mem_of_lookup_some (by simpa [motherOf?] using hq)
    have := hsp.2 (c, q) hq' (c, p) hf
    simp only [bne_iff_ne, ne_eq, beq_iff_eq, Bool.or_eq_true] at this
    rcases this with h1 | h1
    · exact absurd trivial h1
    · rw [hq, h1]

/-- A person has at most one father. -/
theorem father_unique (hsp : f.singleParents = true) {c p q : Qid} (hp : f.Father c p)
    (hq : f.Father c q) : p = q := by
  have h1 := (fatherOf?_eq_some_iff hsp).2 hp
  have h2 := (fatherOf?_eq_some_iff hsp).2 hq
  rw [h1] at h2
  exact Option.some_inj.1 h2

/-- A person has at most one mother. -/
theorem mother_unique (hsp : f.singleParents = true) {c p q : Qid} (hp : f.Mother c p)
    (hq : f.Mother c q) : p = q := by
  have h1 := (motherOf?_eq_some_iff hsp).2 hp
  have h2 := (motherOf?_eq_some_iff hsp).2 hq
  rw [h1] at h2
  exact Option.some_inj.1 h2

/-- **A person has at most two parents** on a validated layer. -/
theorem card_parents_le_two (hsp : f.singleParents = true) (c : Qid) :
    (f.parentsF c).card ≤ 2 := by
  classical
  suffices hex : ∃ p q, ∀ x ∈ f.parentsF c, x = p ∨ x = q by
    obtain ⟨p, q, hpq⟩ := hex
    have hsub : f.parentsF c ⊆ ({p, q} : Finset Qid) := by
      intro x hx
      rcases hpq x hx with rfl | rfl <;> simp
    exact le_trans (Finset.card_le_card hsub)
      (by simpa using Finset.card_insert_le p ({q} : Finset Qid))
  by_cases hf : ∃ p, f.Father c p
  · obtain ⟨p, hp⟩ := hf
    by_cases hm : ∃ q, f.Mother c q
    · obtain ⟨q, hq⟩ := hm
      refine ⟨p, q, fun x hx => ?_⟩
      rcases mem_parentsF.1 hx with hx' | hx'
      · exact Or.inl (father_unique hsp hx' hp)
      · exact Or.inr (mother_unique hsp hx' hq)
    · refine ⟨p, p, fun x hx => ?_⟩
      rcases mem_parentsF.1 hx with hx' | hx'
      · exact Or.inl (father_unique hsp hx' hp)
      · exact absurd ⟨x, hx'⟩ hm
  · by_cases hm : ∃ q, f.Mother c q
    · obtain ⟨q, hq⟩ := hm
      refine ⟨q, q, fun x hx => ?_⟩
      rcases mem_parentsF.1 hx with hx' | hx'
      · exact absurd ⟨x, hx'⟩ hf
      · exact Or.inl (mother_unique hsp hx' hq)
    · refine ⟨c, c, fun x hx => ?_⟩
      rcases mem_parentsF.1 hx with hx' | hx'
      · exact absurd ⟨x, hx'⟩ hf
      · exact absurd ⟨x, hx'⟩ hm

/-! ### Siblings -/

theorem sibling_symm (f : FKB) (a b : Qid) : f.siblingB a b = f.siblingB b a := by
  rw [Bool.eq_iff_iff]
  simp only [siblingB, Bool.and_eq_true, List.any_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq]
  constructor
  · rintro ⟨hne, p, hp, h1, h2⟩; exact ⟨fun hx => hne hx.symm, p, hp, h2, h1⟩
  · rintro ⟨hne, p, hp, h1, h2⟩; exact ⟨fun hx => hne hx.symm, p, hp, h2, h1⟩

theorem sibling_irrefl (f : FKB) (a : Qid) : f.siblingB a a = false := by
  simp [siblingB]

/-- Full siblings are siblings, provided the shared father is a declared item. -/
theorem fullSibling_sibling (h : f.fWellFormed = true) (hsp : f.singleParents = true)
    {a b : Qid} (hab : f.fullSiblingB a b = true) : f.siblingB a b = true := by
  simp only [fullSiblingB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab
  obtain ⟨⟨hne, hfa⟩, _⟩ := hab
  revert hfa
  cases hfx : f.fatherOf? a with
  | none => simp
  | some x =>
    cases hfy : f.fatherOf? b with
    | none => simp
    | some y =>
      intro hxy
      simp only [beq_iff_eq] at hxy
      subst hxy
      have h1 : f.Father a x := (fatherOf?_eq_some_iff hsp).1 hfx
      have h2 : f.Father b x := (fatherOf?_eq_some_iff hsp).1 hfy
      simp only [siblingB, Bool.and_eq_true, List.any_eq_true, bne_iff_ne, ne_eq,
        decide_eq_true_eq]
      exact ⟨hne, x, (fwf_parent h (Or.inl h1)).2, mem_parentsL.2 (Or.inl h1),
        mem_parentsL.2 (Or.inl h2)⟩

/-! ### Children, ancestors and spouses -/

theorem mem_childrenL_iff {p c : Qid} :
    c ∈ f.childrenL p ↔ c ∈ f.base.items ∧ f.Parent c p := by
  simp only [childrenL, List.mem_filter, decide_eq_true_eq]
  exact and_congr_right fun _ => mem_parentsL

/-- A child descends from each of their parents. -/
theorem descendsFromB_of_mem_childrenL (h : f.fWellFormed = true) {p c : Qid}
    (hc : c ∈ f.childrenL p) : f.descendsFromB c p = true :=
  descendsFromB_of_parent h (mem_childrenL_iff.1 hc).2

/-- The listed ancestors of a person are exactly the declared items they descend
from. -/
theorem mem_ancestorsL_iff (h : f.fWellFormed = true) {a b : Qid} :
    b ∈ f.ancestorsL a ↔ b ∈ f.base.items ∧ f.DescendsFrom a b := by
  simp only [ancestorsL, List.mem_filter]
  exact and_congr_right fun _ => descendsFromB_iff h a b

theorem spouseB_symm (f : FKB) (a b : Qid) : f.spouseB a b = f.spouseB b a := by
  simp [spouseB, Bool.or_comm]

/-- On a validated layer nobody is their own spouse. -/
theorem spouseB_irrefl (h : f.noSelfSpouse = true) (a : Qid) : f.spouseB a a = false := by
  simp only [noSelfSpouse, List.all_eq_true, bne_iff_ne, ne_eq] at h
  simp only [spouseB, Bool.or_self, decide_eq_false_iff_not]
  intro hmem
  exact h (a, a) hmem rfl

/-! ### Common ancestors and relatedness -/

theorem mem_commonAncestors_iff (h : f.fWellFormed = true) {a b c : Qid} :
    c ∈ f.commonAncestors a b ↔ f.DescendsFrom a c ∧ f.DescendsFrom b c := by
  simp only [commonAncestors, Finset.mem_inter]
  rw [show (c ∈ f.ancestorClosure a) ↔ f.descendsFromB a c = true by simp [descendsFromB],
    show (c ∈ f.ancestorClosure b) ↔ f.descendsFromB b c = true by simp [descendsFromB],
    descendsFromB_iff h, descendsFromB_iff h]

theorem relatedB_symm (f : FKB) (a b : Qid) : f.relatedB a b = f.relatedB b a := by
  simp [relatedB, commonAncestors, Finset.inter_comm]

/-- Everybody is related to themselves. -/
theorem relatedB_self (f : FKB) (a : Qid) : f.relatedB a a = true := by
  have ha : a ∈ f.ancestorClosure a := by
    simpa [descendsFromB] using descendsFromB_refl f a
  simp only [relatedB, commonAncestors, decide_eq_true_eq, ne_eq]
  exact Finset.ne_empty_of_mem (Finset.mem_inter.2 ⟨ha, ha⟩)

/-- A person is related to each of their ancestors. -/
theorem relatedB_of_descendsFromB {a b : Qid} (hab : f.descendsFromB a b = true) :
    f.relatedB a b = true := by
  have h1 : b ∈ f.ancestorClosure a := by simpa [descendsFromB] using hab
  have h2 : b ∈ f.ancestorClosure b := by
    simpa [descendsFromB] using descendsFromB_refl f b
  simp only [relatedB, commonAncestors, decide_eq_true_eq, ne_eq]
  exact Finset.ne_empty_of_mem (Finset.mem_inter.2 ⟨h1, h2⟩)

/-- Siblings are related. -/
theorem relatedB_of_sibling (h : f.fWellFormed = true) {a b : Qid}
    (hab : f.siblingB a b = true) : f.relatedB a b = true := by
  simp only [siblingB, Bool.and_eq_true, List.any_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at hab
  obtain ⟨_, p, _, h1, h2⟩ := hab
  have hp1 : p ∈ f.ancestorClosure a := by
    simpa [descendsFromB] using descendsFromB_of_parent h (mem_parentsL.1 h1)
  have hp2 : p ∈ f.ancestorClosure b := by
    simpa [descendsFromB] using descendsFromB_of_parent h (mem_parentsL.1 h2)
  simp only [relatedB, commonAncestors, decide_eq_true_eq, ne_eq]
  exact Finset.ne_empty_of_mem (Finset.mem_inter.2 ⟨hp1, hp2⟩)

/-! ### The genealogy is not the taxonomy -/

/-- A validated layer never asserts that an item is a subclass of one of its
parents. -/
theorem parent_not_subclass (h : f.noKinClassConfusion = true) {c p : Qid}
    (hcp : f.Parent c p) : f.base.isSubclassOf c p = false := by
  simp only [noKinClassConfusion, List.all_eq_true, Bool.and_eq_true] at h
  have hmem : (c, p) ∈ f.fathers ++ f.mothers := by
    rcases hcp with hcp | hcp
    · exact List.mem_append_left _ hcp
    · exact List.mem_append_right _ hcp
  simpa using (h (c, p) hmem).1

/-- A validated layer never asserts that an item is an instance of one of its
parents. -/
theorem parent_not_instance (h : f.noKinClassConfusion = true) {c p : Qid}
    (hcp : f.Parent c p) : f.base.isInstanceOf c p = false := by
  simp only [noKinClassConfusion, List.all_eq_true, Bool.and_eq_true] at h
  have hmem : (c, p) ∈ f.fathers ++ f.mothers := by
    rcases hcp with hcp | hcp
    · exact List.mem_append_left _ hcp
    · exact List.mem_append_right _ hcp
  simpa using (h (c, p) hmem).2

/-- Nobody is their own parent on a layer that keeps the genealogy apart from the
taxonomy: `subclass of` is reflexive, so a self-parenthood statement is exactly the
kind of confusion `noKinClassConfusion` rules out. -/
theorem not_parent_self (h : f.noKinClassConfusion = true) (a : Qid) : ¬ f.Parent a a := by
  intro ha
  have := parent_not_subclass h ha
  rw [KB.isSubclassOf_refl] at this
  exact Bool.noConfusion this

/-! ### A worked example: a three-generation family -/

/-- Shorthand for an ordinary Wikidata item. -/
private def Q (s : String) : Qid := Qid.wd s

/-- A stylised fragment: `Q5` (human) with three individuals — a grandmother `Q3`, her
son `Q2`, and his daughter `Q1` — and one spouse statement. -/
def family : FKB where
  base :=
    { name := "family"
      items := [Q "Q1", Q "Q2", Q "Q3", Q "Q4", Q "Q5"]
      levels := [(Q "Q5", 1)]
      inst := [(Q "Q1", Q "Q5"), (Q "Q2", Q "Q5"), (Q "Q3", Q "Q5"), (Q "Q4", Q "Q5")] }
  fathers := [(Q "Q1", Q "Q2")]
  mothers := [(Q "Q1", Q "Q4"), (Q "Q2", Q "Q3")]
  spouses := [(Q "Q2", Q "Q4")]

example : family.fValid = true := by decide

/-- The grandmother is an ancestor of the granddaughter. -/
example : family.descendsFromB (Q "Q1") (Q "Q3") = true := by decide

/-- Ancestry is strict here: the granddaughter is not an ancestor of the
grandmother. -/
example : family.descendsFromB (Q "Q3") (Q "Q1") = false := by decide

/-- The recorded father and mother are found by lookup. -/
example : family.fatherOf? (Q "Q1") = some (Q "Q2") := by decide

example : family.motherOf? (Q "Q1") = some (Q "Q4") := by decide

/-- The two parents of the granddaughter are related to her, but not to each other. -/
example : family.relatedB (Q "Q2") (Q "Q4") = false := by decide

example : family.relatedB (Q "Q1") (Q "Q3") = true := by decide

/-- **Parenthood is not inherited through `instance of`**: every individual of the
fragment is an instance of `human` (`Q5`), and `Q2` is the father of `Q1`, yet `Q3` —
another instance of `human` — is not the father of `Q1`. -/
theorem parent_not_inherited :
    family.base.isInstanceOf (Q "Q2") (Q "Q5") = true ∧
    family.base.isInstanceOf (Q "Q3") (Q "Q5") = true ∧
    family.fatherOf? (Q "Q1") = some (Q "Q2") ∧
    family.fatherOf? (Q "Q1") ≠ some (Q "Q3") := by decide

/-- The children, the ancestors and the spouse of the middle generation. -/
example : family.childrenL (Q "Q2") = [Q "Q1"] := by decide

example : family.ancestorsL (Q "Q1") = [Q "Q1", Q "Q2", Q "Q3", Q "Q4"] := by decide

example : family.spouseB (Q "Q4") (Q "Q2") = true := by decide

/-- A parent is not a sibling. -/
example : family.siblingB (Q "Q1") (Q "Q2") = false := by decide

/-- **Relatedness is not transitive**: the two parents of a child are each related to
the child, but not to each other. -/
theorem related_not_transitive :
    family.relatedB (Q "Q2") (Q "Q1") = true ∧
    family.relatedB (Q "Q1") (Q "Q4") = true ∧
    family.relatedB (Q "Q2") (Q "Q4") = false := by decide

/-- A blended family: `Q1` and `Q6` share a father but have different mothers. -/
def blended : FKB where
  base :=
    { name := "blended"
      items := [Q "Q1", Q "Q2", Q "Q4", Q "Q6", Q "Q7"] }
  fathers := [(Q "Q1", Q "Q2"), (Q "Q6", Q "Q2")]
  mothers := [(Q "Q1", Q "Q4"), (Q "Q6", Q "Q7")]

/-- **Half siblings are siblings but not full siblings.** -/
theorem halfSiblings_not_full :
    blended.fValid = true ∧
    blended.siblingB (Q "Q1") (Q "Q6") = true ∧
    blended.fullSiblingB (Q "Q1") (Q "Q6") = false := by decide

/-- A knowledge base whose kinship layer is a cycle is rejected. -/
def cyclicFamily : FKB where
  base := { name := "cycle", items := [Q "Q1", Q "Q2"] }
  fathers := [(Q "Q1", Q "Q2"), (Q "Q2", Q "Q1")]

example : cyclicFamily.fValid = false := by decide

/-- Two different fathers for the same person are rejected. -/
def twoFathers : FKB where
  base := { name := "two fathers", items := [Q "Q1", Q "Q2", Q "Q3"] }
  fathers := [(Q "Q1", Q "Q2"), (Q "Q1", Q "Q3")]

example : twoFathers.singleParents = false := by decide

end FKB

end Wikidata
