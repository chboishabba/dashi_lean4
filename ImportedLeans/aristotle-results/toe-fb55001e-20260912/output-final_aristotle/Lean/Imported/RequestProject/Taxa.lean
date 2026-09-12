import RequestProject.Engine

/-!
# The taxon layer: `parent taxon` (P171), `taxon rank` (P105) and `taxon name` (P225)

Biological classification is the part of Wikidata that looks most like an ontology and is
least like one.  A taxon — *Homo sapiens*, *Hominidae*, *Mammalia* — is an **item**, not a
class of the ontology: `Wikidata:WikiProject Ontology` is explicit that the biological
hierarchy is built from `parent taxon` (P171) and **not** from `subclass of` (P279), and
that a taxon carries its position in the hierarchy as a value of `taxon rank` (P105)
rather than as a metaclass level.

This file adds that layer on top of the executable knowledge base of
`RequestProject.Engine`.  A `TKB` is a `KB` together with

* `parent taxon` (P171) statements `(taxon, parent)`,
* `taxon rank` (P105) values, drawn from the ranks of `TaxonRank`, and
* `taxon name` (P225) strings.

Everything is computable — `TKB.isDescendantB`, `TKB.rootsOfL`, `TKB.tValid` — and
certified: on a well-formed layer `isDescendantB` decides the reflexive–transitive closure
of the asserted P171 statements (`TKB.isDescendantB_iff`).

The results are:

* descent is a **partial order** on an acyclic layer and its strict part is a strict order
  (`TKB.descent_antisymm`, `TKB.strictDescent_trans`);
* the hierarchy is **well founded** (`TKB.parent_wf`), so every taxon descends from a
  **root**: a taxon with no parent taxon (`TKB.exists_root`);
* **ranks certify acyclicity**: if every taxon carries a `taxon rank` and the ranks
  strictly increase along `parent taxon` — two purely local checks — then no taxon can be
  its own ancestor (`TKB.no_cycle_of_ranks`);
* **a single parent makes a tree**: if no taxon has two different parent taxa then the
  ancestors of a taxon are linearly ordered (`TKB.descent_total_of_functional`) and the
  root of a taxon is unique (`TKB.exists_unique_root`, `TKB.tValid_exists_unique_root`);
* the taxon hierarchy is **not** the taxonomy of the ontology: a valid layer never asserts
  a `parent taxon` statement between items already related by `subclass of` or
  `instance of` (`TKB.parentTaxon_not_taxonomic`);
* `taxon name` (P225) is **injective** on a valid layer (`TKB.taxon_of_name_unique`).

`RequestProject.TaxaLineage` walks the hierarchy — the lineage of a taxon and the lowest
common ancestor of two taxa — and `RequestProject.TaxaExamples` works the lineage of
*Homo sapiens* through the whole layer.
-/

namespace Wikidata

/-- The principal ranks of biological classification, as `taxon rank` (P105) values. -/
inductive TaxonRank where
  /-- species (Q7432) -/
  | species
  /-- genus (Q34740) -/
  | genus
  /-- family (Q35409) -/
  | family
  /-- order (Q36602) -/
  | order
  /-- class (Q37517) -/
  | class_
  /-- phylum (Q38348) -/
  | phylum
  /-- kingdom (Q36732) -/
  | kingdom
  /-- domain (Q146481) -/
  | domain
deriving DecidableEq, Repr, Inhabited

namespace TaxonRank

/-- The height of a rank in the scale: species is `0`, domain is `7`. -/
def level : TaxonRank → ℕ
  | .species => 0
  | .genus => 1
  | .family => 2
  | .order => 3
  | .class_ => 4
  | .phylum => 5
  | .kingdom => 6
  | .domain => 7

/-- The Wikidata item denoting the rank. -/
def qid : TaxonRank → Qid
  | .species => .wd "Q7432"
  | .genus => .wd "Q34740"
  | .family => .wd "Q35409"
  | .order => .wd "Q36602"
  | .class_ => .wd "Q37517"
  | .phylum => .wd "Q38348"
  | .kingdom => .wd "Q36732"
  | .domain => .wd "Q146481"

/-- The English name of the rank. -/
def label : TaxonRank → String
  | .species => "species"
  | .genus => "genus"
  | .family => "family"
  | .order => "order"
  | .class_ => "class"
  | .phylum => "phylum"
  | .kingdom => "kingdom"
  | .domain => "domain"

/-- The scale is a scale: distinct ranks sit at distinct heights. -/
theorem level_injective {r r' : TaxonRank} (h : r.level = r'.level) : r = r' := by
  cases r <;> cases r' <;> simp_all [level]

/-- Distinct ranks are distinct Wikidata items. -/
theorem qid_injective {r r' : TaxonRank} (h : r.qid = r'.qid) : r = r' := by
  cases r <;> cases r' <;> simp_all [qid]

end TaxonRank

/-- A finite, executable **taxon layer** over a knowledge base: the `parent taxon` (P171)
statements, the `taxon rank` (P105) values and the `taxon name` (P225) strings. -/
structure TKB where
  /-- The underlying item ontology (taxonomy). -/
  base : KB
  /-- `parent taxon` (P171) statements, written `(taxon, parent)`. -/
  parents : List (Qid × Qid) := []
  /-- `taxon rank` (P105) values. -/
  ranks : List (Qid × TaxonRank) := []
  /-- `taxon name` (P225) values: the scientific name of the taxon. -/
  names : List (Qid × String) := []
deriving Repr, DecidableEq, Inhabited

namespace TKB

variable (k : TKB)

/-! ### The computational engine -/

/-- The parent taxa (P171) asserted for a taxon. -/
def parentsL (q : Qid) : List Qid := (k.parents.filter (fun r => r.1 == q)).map Prod.snd

/-- The parent taxa of a taxon, as a `Finset`. -/
def parentsF (q : Qid) : Finset Qid := (k.parentsL q).toFinset

/-- The taxa whose asserted parent taxon is the given one. -/
def childrenL (q : Qid) : List Qid := (k.parents.filter (fun r => r.2 == q)).map Prod.fst

/-- All ancestors of a taxon, computed by saturating the P171 graph. -/
def ancestorClosure (q : Qid) : Finset Qid := Reach.reach k.parentsF k.base.allF q

/-- Decides (reflexive) descent: `a` is `b`, or a child of a child of … of `b`. -/
def isDescendantB (a b : Qid) : Bool := b ∈ k.ancestorClosure a

/-- Decides *strict* descent. -/
def isStrictDescendantB (a b : Qid) : Bool := k.isDescendantB a b && a != b

/-- The `taxon rank` (P105) of a taxon, if it has one. -/
def rankOf? (q : Qid) : Option TaxonRank := k.ranks.lookup q

/-- The `taxon name` (P225) of a taxon, if it has one. -/
def nameOf? (q : Qid) : Option String := k.names.lookup q

/-- The taxon carrying a given scientific name, if the layer records one. -/
def taxonOfName? (n : String) : Option Qid :=
  (k.names.filter (fun r => r.2 == n)).head?.map Prod.fst

/-- A taxon is a **root** when it has no parent taxon. -/
def isRootB (q : Qid) : Bool := k.parentsL q == []

/-- The roots a taxon descends from. -/
def rootsOfL (a : Qid) : List Qid :=
  k.base.items.filter (fun b => k.isDescendantB a b && k.isRootB b)

/-- The number of ancestors of a taxon (itself included): the measure that makes the
hierarchy well founded. -/
def taxonDepth (a : Qid) : ℕ := (k.ancestorClosure a).card

/-! ### The validator -/

/-- All taxon statements mention declared items. -/
def tWellFormed : Bool :=
  k.base.wellFormed &&
  k.parents.all (fun r => r.1 ∈ k.base.items && r.2 ∈ k.base.items) &&
  k.ranks.all (fun r => r.1 ∈ k.base.items) &&
  k.names.all (fun r => r.1 ∈ k.base.items)

/-- The `parent taxon` graph has no cycles: no taxon is its own parent, and no two distinct
taxa descend from one another. -/
def tAcyclic : Bool :=
  k.parents.all (fun r => r.1 != r.2) &&
  k.base.items.all (fun a => k.base.items.all
    (fun b => !(k.isDescendantB a b && k.isDescendantB b a) || a == b))

/-- No taxon has two different parent taxa. -/
def singleParent : Bool :=
  k.parents.all (fun r => k.parents.all (fun r' => !(r.1 == r'.1) || r.2 == r'.2))

/-- The `taxon rank` values strictly increase along `parent taxon`: a genus does not sit
inside a species. -/
def ranksStrict : Bool :=
  k.parents.all (fun r =>
    match k.rankOf? r.1, k.rankOf? r.2 with
    | some p, some q => decide (p.level < q.level)
    | _, _ => true)

/-- Every declared item carries a `taxon rank`. -/
def ranksTotal : Bool := k.base.items.all (fun a => (k.rankOf? a).isSome)

/-- Distinct taxa carry distinct scientific names. -/
def namesUnique : Bool :=
  k.names.all (fun r => k.names.all (fun r' => !(r.2 == r'.2) || r.1 == r'.1))

/-- The taxon hierarchy is not the taxonomy: no `parent taxon` statement relates two items
that are already related by `subclass of` or `instance of`. -/
def noTaxonomyConfusion : Bool :=
  k.parents.all (fun r =>
    !k.base.isSubclassOf r.1 r.2 && !k.base.isSubclassOf r.2 r.1 &&
    !k.base.isInstanceOf r.1 r.2 && !k.base.isInstanceOf r.2 r.1)

/-- The checks the taxon layer itself has to pass. -/
def tLayerValid : Bool :=
  k.tWellFormed && k.tAcyclic && k.singleParent && k.ranksStrict &&
    k.namesUnique && k.noTaxonomyConfusion

/-- The full validity check for a taxon layer: a valid ontology carrying a valid taxon
hierarchy. -/
def tValid : Bool := k.base.valid && k.tLayerValid

/-! ### Semantics -/

/-- The asserted `parent taxon` (P171) statements, as a relation. -/
def ParentTaxon (a b : Qid) : Prop := (a, b) ∈ k.parents

/-- Derived descent: `a` descends from `b`, i.e. the reflexive–transitive closure of the
asserted `parent taxon` statements. -/
def DescendsFrom (a b : Qid) : Prop := Relation.ReflTransGen k.ParentTaxon a b

/-- The asserted `taxon rank` (P105) statements. -/
def HasRank (a : Qid) (r : TaxonRank) : Prop := k.rankOf? a = some r

variable {k}

theorem mem_parentsF {a b : Qid} : b ∈ k.parentsF a ↔ k.ParentTaxon a b := by
  simp [parentsF, parentsL, ParentTaxon, List.mem_filter, List.mem_map]

theorem mem_parentsL {a b : Qid} : b ∈ k.parentsL a ↔ k.ParentTaxon a b := by
  simp [parentsL, ParentTaxon, List.mem_filter, List.mem_map]

/-- The children list is exactly the converse of `parent taxon`. -/
theorem mem_childrenL {a b : Qid} : a ∈ k.childrenL b ↔ k.ParentTaxon a b := by
  simp [childrenL, ParentTaxon, List.mem_filter, List.mem_map]

theorem succ_eq_parentTaxon (k : TKB) : (fun u v => v ∈ k.parentsF u) = k.ParentTaxon := by
  funext u v; exact propext mem_parentsF

theorem twf_base (h : k.tWellFormed = true) : k.base.wellFormed = true := by
  simp only [tWellFormed, Bool.and_eq_true] at h; tauto

/-- Both endpoints of a P171 statement of a well-formed layer are items. -/
theorem twf_parents (h : k.tWellFormed = true) {a b : Qid} (hab : k.ParentTaxon a b) :
    a ∈ k.base.items ∧ b ∈ k.base.items := by
  simp only [tWellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  simpa using h.1.1.2 (a, b) hab

theorem parentsF_subset_allF (h : k.tWellFormed = true) (y : Qid) :
    k.parentsF y ⊆ k.base.allF := by
  intro b hb
  simpa [KB.allF] using (twf_parents h (mem_parentsF.1 hb)).2

theorem parentsF_eq_empty_of_not_mem (h : k.tWellFormed = true) {a : Qid}
    (ha : a ∉ k.base.items) : k.parentsF a = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 fun b hb => ?_
  exact ha (twf_parents h (mem_parentsF.1 hb)).1

/-- **Certified descent computation**: in a well-formed layer the Boolean check
`isDescendantB` decides the reflexive–transitive closure of the asserted P171 statements. -/
theorem isDescendantB_iff (h : k.tWellFormed = true) (a b : Qid) :
    k.isDescendantB a b = true ↔ k.DescendsFrom a b := by
  have hcl := Reach.mem_reach_iff_of_closed k.parentsF (parentsF_subset_allF h)
    (fun y hy => parentsF_eq_empty_of_not_mem h (by simpa [KB.allF] using hy)) a b
  rw [succ_eq_parentTaxon] at hcl
  simpa [isDescendantB, ancestorClosure, DescendsFrom] using hcl

theorem isDescendantB_refl (k : TKB) (a : Qid) : k.isDescendantB a a = true := by
  simpa [isDescendantB, ancestorClosure] using Reach.mem_reach_self k.parentsF k.base.allF a

theorem isDescendantB_of_parent (h : k.tWellFormed = true) {a b : Qid} (hab : k.ParentTaxon a b) :
    k.isDescendantB a b = true :=
  (isDescendantB_iff h a b).2 (Relation.ReflTransGen.single hab)

theorem isDescendantB_trans (h : k.tWellFormed = true) {a b c : Qid}
    (hab : k.isDescendantB a b = true) (hbc : k.isDescendantB b c = true) :
    k.isDescendantB a c = true :=
  (isDescendantB_iff h a c).2
    (((isDescendantB_iff h a b).1 hab).trans ((isDescendantB_iff h b c).1 hbc))

/-- Every ancestor of a declared taxon is again a declared item. -/
theorem mem_items_of_descent (h : k.tWellFormed = true) {a b : Qid}
    (ha : a ∈ k.base.items) (hab : k.DescendsFrom a b) : b ∈ k.base.items := by
  induction hab with
  | refl => exact ha
  | tail _ hstep _ => exact (twf_parents h hstep).2

/-! ### The order and its well-foundedness -/

/-- Antisymmetry of descent on an acyclic layer. -/
theorem descent_antisymm (h : k.tWellFormed = true) (hac : k.tAcyclic = true) {a b : Qid}
    (hab : k.isDescendantB a b = true) (hba : k.isDescendantB b a = true) : a = b := by
  by_cases hne : a = b
  · exact hne
  · exfalso
    by_cases ha : a ∈ k.base.items
    · have hb : b ∈ k.base.items := mem_items_of_descent h ha ((isDescendantB_iff h a b).1 hab)
      simp only [tAcyclic, Bool.and_eq_true, List.all_eq_true] at hac
      have := hac.2 a ha b hb
      simp [hab, hba, hne] at this
    · have hp : k.parentsF a = ∅ := parentsF_eq_empty_of_not_mem h ha
      have : k.DescendsFrom a b := (isDescendantB_iff h a b).1 hab
      rcases Relation.reflTransGen_iff_eq_or_transGen.1 this with rfl | hgen
      · exact hne rfl
      · obtain ⟨c, hc, -⟩ := Relation.TransGen.head'_iff.1 hgen
        exact absurd (mem_parentsF.2 hc) (by simp [hp])

theorem isStrictDescendantB_irrefl (k : TKB) (a : Qid) : k.isStrictDescendantB a a = false := by
  simp [isStrictDescendantB]

/-- Strict descent is asymmetric on an acyclic layer. -/
theorem strictDescent_asymm (h : k.tWellFormed = true) (hac : k.tAcyclic = true) {a b : Qid}
    (hab : k.isStrictDescendantB a b = true) (hba : k.isStrictDescendantB b a = true) : False := by
  simp only [isStrictDescendantB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab hba
  exact hab.2 (descent_antisymm h hac hab.1 hba.1)

/-- Strict descent is transitive on an acyclic layer. -/
theorem strictDescent_trans (h : k.tWellFormed = true) (hac : k.tAcyclic = true) {a b c : Qid}
    (hab : k.isStrictDescendantB a b = true) (hbc : k.isStrictDescendantB b c = true) :
    k.isStrictDescendantB a c = true := by
  simp only [isStrictDescendantB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab hbc ⊢
  refine ⟨isDescendantB_trans h hab.1 hbc.1, ?_⟩
  rintro rfl
  exact hbc.2 (descent_antisymm h hac hbc.1 hab.1)

theorem ancestorClosure_subset (h : k.tWellFormed = true) {a b : Qid}
    (hab : k.isDescendantB a b = true) : k.ancestorClosure b ⊆ k.ancestorClosure a := by
  intro c hc
  have hbc : k.isDescendantB b c = true := by simpa [isDescendantB] using hc
  simpa [isDescendantB] using isDescendantB_trans h hab hbc

/-- **Going up the hierarchy strictly decreases the depth**: a taxon has strictly more
ancestors than any taxon it strictly descends from. -/
theorem taxonDepth_lt (h : k.tWellFormed = true) (hac : k.tAcyclic = true) {a b : Qid}
    (hab : k.isStrictDescendantB a b = true) : k.taxonDepth b < k.taxonDepth a := by
  have hab' : k.isDescendantB a b = true := by
    simp only [isStrictDescendantB, Bool.and_eq_true] at hab
    exact hab.1
  refine Finset.card_lt_card ⟨ancestorClosure_subset h hab', fun hsub => ?_⟩
  have ha : a ∈ k.ancestorClosure a := by simpa [isDescendantB] using isDescendantB_refl k a
  have hba : k.isDescendantB b a = true := by simpa [isDescendantB] using hsub ha
  simp only [isStrictDescendantB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab
  exact hab.2 (descent_antisymm h hac hab' hba)

/-- **The taxon hierarchy is well founded**: there is no infinite ascending chain of parent
taxa, so one may reason by induction up the hierarchy. -/
theorem parent_wf (h : k.tWellFormed = true) (hac : k.tAcyclic = true) :
    WellFounded (fun b a : Qid => k.isStrictDescendantB a b = true) := by
  refine Subrelation.wf (r := InvImage (· < ·) k.taxonDepth) ?_ (InvImage.wf _ Nat.lt_wfRel.wf)
  intro b a hab
  exact taxonDepth_lt h hac hab

/-- On an acyclic layer an asserted `parent taxon` statement is strict descent. -/
theorem strictDescent_of_parent (h : k.tWellFormed = true) (hac : k.tAcyclic = true)
    {a b : Qid} (hab : k.ParentTaxon a b) : k.isStrictDescendantB a b = true := by
  have hd : k.isDescendantB a b = true := isDescendantB_of_parent h hab
  simp only [isStrictDescendantB, Bool.and_eq_true, bne_iff_ne, ne_eq]
  refine ⟨hd, ?_⟩
  rintro rfl
  simp only [tAcyclic, Bool.and_eq_true, List.all_eq_true, bne_iff_ne, ne_eq] at hac
  exact hac.1 (a, a) hab rfl

/-- Every taxon has at least one ancestor, namely itself. -/
theorem taxonDepth_pos (k : TKB) (a : Qid) : 0 < k.taxonDepth a :=
  Finset.card_pos.2 ⟨a, by simpa [isDescendantB] using isDescendantB_refl k a⟩

/-- **Every taxon has a root**: on a well-formed acyclic layer every taxon descends from a
taxon with no parent taxon at all. -/
theorem exists_root (h : k.tWellFormed = true) (hac : k.tAcyclic = true) (a : Qid) :
    ∃ b, k.isDescendantB a b = true ∧ k.isRootB b = true := by
  suffices key : ∀ n a, k.taxonDepth a ≤ n →
      ∃ b, k.isDescendantB a b = true ∧ k.isRootB b = true by
    exact key (k.taxonDepth a) a le_rfl
  intro n
  induction n with
  | zero =>
      intro a ha
      exact absurd (taxonDepth_pos k a) (by omega)
  | succ m ih =>
      intro a ha
      by_cases hroot : k.isRootB a = true
      · exact ⟨a, isDescendantB_refl k a, hroot⟩
      · obtain ⟨p, hp⟩ : ∃ p, p ∈ k.parentsL a := by
          simp only [isRootB, beq_iff_eq] at hroot
          exact List.exists_mem_of_ne_nil _ hroot
        have hpa : k.ParentTaxon a p := mem_parentsL.1 hp
        have hlt : k.taxonDepth p < k.taxonDepth a :=
          taxonDepth_lt h hac (strictDescent_of_parent h hac hpa)
        obtain ⟨b, hb, hrb⟩ := ih p (by omega)
        exact ⟨b, isDescendantB_trans h (isDescendantB_of_parent h hpa) hb, hrb⟩

/-! ### Ranks certify acyclicity -/

theorem rank_lt_of_parent (h : k.ranksStrict = true) {a b : Qid} (hab : k.ParentTaxon a b)
    {p q : TaxonRank} (hp : k.rankOf? a = some p) (hq : k.rankOf? b = some q) :
    p.level < q.level := by
  simp only [ranksStrict, List.all_eq_true] at h
  have := h (a, b) hab
  simp only [hp, hq, decide_eq_true_eq] at this
  exact this

theorem rank_isSome_of_mem (h : k.ranksTotal = true) {a : Qid} (ha : a ∈ k.base.items) :
    (k.rankOf? a).isSome = true := by
  simp only [ranksTotal, List.all_eq_true] at h
  exact h a ha

/-- Along a nonempty chain of `parent taxon` statements the ranks strictly increase. -/
theorem rank_lt_of_transGen (hwf : k.tWellFormed = true) (hstrict : k.ranksStrict = true)
    (htot : k.ranksTotal = true) {a b : Qid} (hab : Relation.TransGen k.ParentTaxon a b) :
    ∃ p q, k.rankOf? a = some p ∧ k.rankOf? b = some q ∧ p.level < q.level := by
  induction hab with
  | single hstep =>
      obtain ⟨ha, hb⟩ := twf_parents hwf hstep
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (rank_isSome_of_mem htot ha)
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (rank_isSome_of_mem htot hb)
      exact ⟨p, q, hp, hq, rank_lt_of_parent hstrict hstep hp hq⟩
  | tail _ hstep ih =>
      obtain ⟨p, r, hp, hr, hpr⟩ := ih
      obtain ⟨-, hb⟩ := twf_parents hwf hstep
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (rank_isSome_of_mem htot hb)
      exact ⟨p, q, hp, hq, lt_trans hpr (rank_lt_of_parent hstrict hstep hr hq)⟩

/-- **Consistent ranks rule out cycles**: if every taxon carries a `taxon rank` and the
ranks increase along every asserted `parent taxon` statement, then no taxon is a strict
ancestor of itself. -/
theorem no_cycle_of_ranks (hwf : k.tWellFormed = true) (hstrict : k.ranksStrict = true)
    (htot : k.ranksTotal = true) (a : Qid) : ¬ Relation.TransGen k.ParentTaxon a a := by
  intro hgen
  obtain ⟨p, q, hp, hq, hlt⟩ := rank_lt_of_transGen hwf hstrict htot hgen
  rw [hp] at hq
  exact absurd hlt (by simp [Option.some_inj.1 hq])

/-- Ranks are monotone along descent as well: an ancestor never has a lower rank. -/
theorem rank_le_of_descent (hwf : k.tWellFormed = true) (hstrict : k.ranksStrict = true)
    (htot : k.ranksTotal = true) {a b : Qid} (hab : k.DescendsFrom a b) {p q : TaxonRank}
    (hp : k.rankOf? a = some p) (hq : k.rankOf? b = some q) : p.level ≤ q.level := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hab with rfl | hgen
  · rw [hp] at hq
    exact le_of_eq (congrArg TaxonRank.level (Option.some_inj.1 hq))
  · obtain ⟨p', q', hp', hq', hlt⟩ := rank_lt_of_transGen hwf hstrict htot hgen
    rw [hp] at hp'; rw [hq] at hq'
    have e1 : p = p' := Option.some_inj.1 hp'
    have e2 : q = q' := Option.some_inj.1 hq'
    subst e1; subst e2
    omega

/-! ### One parent makes a tree -/

/-- The `singleParent` check says exactly that `parent taxon` is a partial function. -/
theorem parent_functional (h : k.singleParent = true) {a b c : Qid}
    (hb : k.ParentTaxon a b) (hc : k.ParentTaxon a c) : b = c := by
  simp only [singleParent, List.all_eq_true] at h
  have := h (a, b) hb (a, c) hc
  simpa using this

/-- **A hierarchy with single parents is a tree**: the ancestors of a taxon are linearly
ordered by descent. -/
theorem descent_total_of_functional (h : k.singleParent = true) {a b c : Qid}
    (hab : k.DescendsFrom a b) (hac : k.DescendsFrom a c) :
    k.DescendsFrom b c ∨ k.DescendsFrom c b := by
  induction hab using Relation.ReflTransGen.head_induction_on with
  | refl => exact Or.inl hac
  | head hstep _ ih =>
      rcases Relation.ReflTransGen.cases_head hac with rfl | ⟨e, hae, hec⟩
      · exact Or.inr (Relation.ReflTransGen.head hstep (by assumption))
      · exact ih (by rwa [parent_functional h hae hstep] at hec)

/-- A root taxon is reached from itself only. -/
theorem eq_of_descent_root {a b : Qid} (hab : k.DescendsFrom a b) (ha : k.isRootB a = true) :
    a = b := by
  rcases Relation.ReflTransGen.cases_head hab with rfl | ⟨e, hae, -⟩
  · rfl
  · exact absurd (mem_parentsL.2 hae) (by simp only [isRootB, beq_iff_eq] at ha; simp [ha])

/-- **The root of a taxon is unique** when no taxon has two parent taxa. -/
theorem root_unique (h : k.singleParent = true) {a b c : Qid}
    (hab : k.DescendsFrom a b) (hac : k.DescendsFrom a c) (hb : k.isRootB b = true)
    (hc : k.isRootB c = true) : b = c := by
  rcases descent_total_of_functional h hab hac with hbc | hcb
  · exact eq_of_descent_root hbc hb
  · exact (eq_of_descent_root hcb hc).symm

/-- Combining the two: on a well-formed, acyclic layer with single parents, every taxon
descends from **exactly one** root. -/
theorem exists_unique_root (h : k.tWellFormed = true) (hac : k.tAcyclic = true)
    (hsp : k.singleParent = true) (a : Qid) :
    ∃! b, k.isDescendantB a b = true ∧ k.isRootB b = true := by
  obtain ⟨b, hb, hrb⟩ := exists_root h hac a
  refine ⟨b, ⟨hb, hrb⟩, ?_⟩
  rintro c ⟨hc, hrc⟩
  exact root_unique hsp ((isDescendantB_iff h a c).1 hc) ((isDescendantB_iff h a b).1 hb) hrc hrb

/-! ### The taxon hierarchy is not the taxonomy -/

/-- On a valid layer, no `parent taxon` statement relates two items already related by
`subclass of` or `instance of`: *Homo* is not a subclass of *Hominidae*, it is a child of it
in a different hierarchy. -/
theorem parentTaxon_not_taxonomic (h : k.noTaxonomyConfusion = true) {a b : Qid}
    (hab : k.ParentTaxon a b) :
    k.base.isSubclassOf a b = false ∧ k.base.isSubclassOf b a = false ∧
      k.base.isInstanceOf a b = false ∧ k.base.isInstanceOf b a = false := by
  simp only [noTaxonomyConfusion, List.all_eq_true] at h
  have := h (a, b) hab
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

/-! ### Scientific names -/

/-- **`taxon name` identifies the taxon**: on a layer passing `namesUnique`, two taxa with
the same scientific name are the same taxon. -/
theorem taxon_of_name_unique (h : k.namesUnique = true) {a b : Qid} {n : String}
    (ha : (a, n) ∈ k.names) (hb : (b, n) ∈ k.names) : a = b := by
  simp only [namesUnique, List.all_eq_true] at h
  have := h (a, n) ha (b, n) hb
  simpa using this

/-! ### Consequences of validity -/

theorem tValid_tWellFormed (h : k.tValid = true) : k.tWellFormed = true := by
  simp only [tValid, tLayerValid, Bool.and_eq_true] at h; tauto

theorem tValid_tAcyclic (h : k.tValid = true) : k.tAcyclic = true := by
  simp only [tValid, tLayerValid, Bool.and_eq_true] at h; tauto

theorem tValid_singleParent (h : k.tValid = true) : k.singleParent = true := by
  simp only [tValid, tLayerValid, Bool.and_eq_true] at h; tauto

theorem tValid_ranksStrict (h : k.tValid = true) : k.ranksStrict = true := by
  simp only [tValid, tLayerValid, Bool.and_eq_true] at h; tauto

theorem tValid_namesUnique (h : k.tValid = true) : k.namesUnique = true := by
  simp only [tValid, tLayerValid, Bool.and_eq_true] at h; tauto

theorem tValid_noTaxonomyConfusion (h : k.tValid = true) : k.noTaxonomyConfusion = true := by
  simp only [tValid, tLayerValid, Bool.and_eq_true] at h; tauto

theorem tValid_base (h : k.tValid = true) : k.base.valid = true := by
  simp only [tValid, Bool.and_eq_true] at h; tauto

/-- On a valid taxon layer every taxon descends from exactly one root. -/
theorem tValid_exists_unique_root (h : k.tValid = true) (a : Qid) :
    ∃! b, k.isDescendantB a b = true ∧ k.isRootB b = true :=
  exists_unique_root (tValid_tWellFormed h) (tValid_tAcyclic h) (tValid_singleParent h) a

end TKB

end Wikidata
