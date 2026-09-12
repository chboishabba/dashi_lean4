import RequestProject.Engine

/-!
# Least common subsumers

A basic question one asks of any class hierarchy is: given two classes, what is
the most specific class that subsumes both?  In description-logic terminology it
is the **least common subsumer**, and on Wikidata it is what one is looking for
when asking "what do these two items have in common?".

This file develops it for the Wikidata hierarchy.  A *common superclass* of `a`
and `b` is a class both are subclasses of; a *least common subsumer* is a common
superclass that is a subclass of every common superclass.  The results:

* a least common subsumer is **unique** when it exists
  (`Wikidata.Ontology.isLCS_unique`), because the derived hierarchy is
  antisymmetric — so one may speak of *the* least common subsumer;
* it is symmetric, idempotent, and equal to `b` whenever `a` is a subclass of
  `b`;
* everything that instantiates both `a` and `b` instantiates their least common
  subsumer, which is the reason the notion is useful;
* two items at **different metaclass levels have no common superclass at all**,
  hence no least common subsumer;
* a **least common subsumer need not exist**: on the executable side the
  candidates are computed by `Wikidata.KB.lcsCandidates`, this list is proved to
  contain exactly the least common subsumers (so it has at most one element),
  and a worked fragment with genuine multiple inheritance is exhibited in which
  it is empty — two classes with two incomparable most specific common
  superclasses.
-/

namespace Wikidata

namespace Ontology

variable {I : Type*} {O : Ontology I}

/-- A *common superclass* of `a` and `b`: a class both are subclasses of. -/
def IsCommonSuperclass (O : Ontology I) (a b c : I) : Prop :=
  O.SubclassOf a c ∧ O.SubclassOf b c

/-- A *least common subsumer* of `a` and `b`: a common superclass which is a
subclass of every common superclass, i.e. the most specific one. -/
def IsLCS (O : Ontology I) (a b c : I) : Prop :=
  O.IsCommonSuperclass a b c ∧ ∀ d, O.IsCommonSuperclass a b d → O.SubclassOf c d

theorem IsCommonSuperclass.symm {a b c : I} (h : O.IsCommonSuperclass a b c) :
    O.IsCommonSuperclass b a c := ⟨h.2, h.1⟩

/-- **Uniqueness**: two least common subsumers of the same pair coincide. -/
theorem isLCS_unique {a b c c' : I} (h : O.IsLCS a b c) (h' : O.IsLCS a b c') : c = c' :=
  subclassOf_antisymm (h.2 c' h'.1) (h'.2 c h.1)

theorem isLCS_symm {a b c : I} (h : O.IsLCS a b c) : O.IsLCS b a c :=
  ⟨h.1.symm, fun d hd => h.2 d hd.symm⟩

/-- A class is its own least common subsumer. -/
theorem isLCS_self (a : I) : O.IsLCS a a a :=
  ⟨⟨subclassOf_refl a, subclassOf_refl a⟩, fun _ hd => hd.1⟩

/-- If `a` is a subclass of `b` then `b` is the least common subsumer of the two. -/
theorem isLCS_of_subclassOf {a b : I} (h : O.SubclassOf a b) : O.IsLCS a b b :=
  ⟨⟨h, subclassOf_refl b⟩, fun _ hd => hd.2⟩

/-- The least common subsumer of `a` and `b` is a superclass of both, so **every
instance of both is an instance of it**. -/
theorem instanceOf_isLCS {x a b c : I} (hxa : O.InstanceOf x a) (hc : O.IsLCS a b c) :
    O.InstanceOf x c := instanceOf_trans_subclassOf hxa hc.1.1

/-- A common superclass forces the two items to sit at the same metaclass level. -/
theorem level_eq_of_isCommonSuperclass {a b c : I} (h : O.IsCommonSuperclass a b c) :
    O.level a = O.level b := (level_subclassOf h.1).trans (level_subclassOf h.2).symm

/-- **Items at different metaclass levels have no common superclass**, so in
particular no least common subsumer: a class and a metaclass are never
generalised by a single class. -/
theorem not_isCommonSuperclass_of_level_ne {a b c : I} (h : O.level a ≠ O.level b) :
    ¬ O.IsCommonSuperclass a b c := fun hc => h (level_eq_of_isCommonSuperclass hc)

theorem not_isLCS_of_level_ne {a b c : I} (h : O.level a ≠ O.level b) : ¬ O.IsLCS a b c :=
  fun hc => not_isCommonSuperclass_of_level_ne h hc.1

/-- The least common subsumer sits at the same level as the two classes. -/
theorem level_isLCS {a b c : I} (h : O.IsLCS a b c) : O.level c = O.level a :=
  (level_subclassOf h.1.1).symm

/-- Transporting the least common subsumer along a superclass: if `c` is the least
common subsumer of `a` and `b` and `a` is a subclass of `b`, then `c = b`. -/
theorem isLCS_eq_of_subclassOf {a b c : I} (hab : O.SubclassOf a b) (h : O.IsLCS a b c) :
    c = b := isLCS_unique h (isLCS_of_subclassOf hab)

end Ontology

/-! ## The executable side -/

namespace KB

variable {kb : KB}

/-- In a well-formed base, following `subclass of` statements out of an item stays
inside the base. -/
theorem mem_items_of_subclassOf (hwf : kb.wellFormed = true) {a b : Qid} (ha : a ∈ kb.items)
    (h : Relation.ReflTransGen kb.Sub a b) : b ∈ kb.items := by
  induction h with
  | refl => exact ha
  | tail _ hbc _ => exact (wf_sub hwf hbc).2

variable (kb)

/-- The common superclasses of two items, among the items of the base. -/
def commonSupers (a b : Qid) : List Qid :=
  kb.items.filter (fun c => kb.isSubclassOf a c && kb.isSubclassOf b c)

/-- The least common subsumers of two items: the common superclasses that are
subclasses of every common superclass. -/
def lcsCandidates (a b : Qid) : List Qid :=
  (kb.commonSupers a b).filter (fun c => (kb.commonSupers a b).all (fun d => kb.isSubclassOf c d))

/-- The least common subsumer, when there is one. -/
def lcs? (a b : Qid) : Option Qid := (kb.lcsCandidates a b).head?

variable {kb}

theorem mem_commonSupers {a b c : Qid} :
    c ∈ kb.commonSupers a b ↔
      c ∈ kb.items ∧ kb.isSubclassOf a c = true ∧ kb.isSubclassOf b c = true := by
  simp [commonSupers, List.mem_filter]

/-- Membership in `commonSupers` is exactly being a common superclass, for items of
a valid base. -/
theorem mem_commonSupers_iff (hv : kb.valid = true) {a b : Qid} (ha : a ∈ kb.items)
    {c : Qid} : c ∈ kb.commonSupers a b ↔ (kb.toOntology hv).IsCommonSuperclass a b c := by
  have hwf := valid_wellFormed hv
  rw [mem_commonSupers]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨(isSubclassOf_iff_subclassOf hv a c).1 h1, (isSubclassOf_iff_subclassOf hv b c).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mem_items_of_subclassOf hwf ha h1, (isSubclassOf_iff_subclassOf hv a c).2 h1,
      (isSubclassOf_iff_subclassOf hv b c).2 h2⟩

/-- **The computed candidates are exactly the least common subsumers.** -/
theorem mem_lcsCandidates_iff (hv : kb.valid = true) {a b : Qid} (ha : a ∈ kb.items)
    {c : Qid} :
    c ∈ kb.lcsCandidates a b ↔ (kb.toOntology hv).IsLCS a b c := by
  simp only [lcsCandidates, List.mem_filter, List.all_eq_true]
  constructor
  · rintro ⟨hc, hall⟩
    refine ⟨(mem_commonSupers_iff hv ha).1 hc, ?_⟩
    intro d hd
    have hdmem : d ∈ kb.commonSupers a b := (mem_commonSupers_iff hv ha).2 hd
    exact (isSubclassOf_iff_subclassOf hv c d).1 (by simpa using hall d hdmem)
  · rintro ⟨hc, hmin⟩
    refine ⟨(mem_commonSupers_iff hv ha).2 hc, ?_⟩
    intro d hd
    have hd' : (kb.toOntology hv).IsCommonSuperclass a b d := (mem_commonSupers_iff hv ha).1 hd
    simpa using (isSubclassOf_iff_subclassOf hv c d).2 (hmin d hd')

/-- Hence the computed list has at most one element. -/
theorem lcsCandidates_subsingleton (hv : kb.valid = true) {a b : Qid} (ha : a ∈ kb.items)
    {c c' : Qid} (hc : c ∈ kb.lcsCandidates a b)
    (hc' : c' ∈ kb.lcsCandidates a b) : c = c' :=
  Ontology.isLCS_unique ((mem_lcsCandidates_iff hv ha).1 hc)
    ((mem_lcsCandidates_iff hv ha).1 hc')

/-- **Soundness of the computation**: whatever `lcs?` returns really is the least
common subsumer. -/
theorem isLCS_of_lcs?_eq_some (hv : kb.valid = true) {a b c : Qid} (ha : a ∈ kb.items)
    (h : kb.lcs? a b = some c) : (kb.toOntology hv).IsLCS a b c :=
  (mem_lcsCandidates_iff hv ha).1 (List.mem_of_mem_head? h)

/-- **Completeness of the computation**: if there is a least common subsumer, the
computation finds it. -/
theorem lcs?_eq_some_of_isLCS (hv : kb.valid = true) {a b c : Qid} (ha : a ∈ kb.items)
    (h : (kb.toOntology hv).IsLCS a b c) : kb.lcs? a b = some c := by
  have hc : c ∈ kb.lcsCandidates a b := (mem_lcsCandidates_iff hv ha).2 h
  obtain ⟨d, hd⟩ : ∃ d, kb.lcs? a b = some d := by
    cases hl : kb.lcsCandidates a b with
    | nil => simp [hl] at hc
    | cons x xs => exact ⟨x, by simp [lcs?, hl]⟩
  have hd' : d ∈ kb.lcsCandidates a b := List.mem_of_mem_head? hd
  rw [hd, lcsCandidates_subsingleton hv ha hd' hc]

/-- **No least common subsumer**: if the computation finds no candidate, none
exists. -/
theorem not_isLCS_of_lcsCandidates_eq_nil (hv : kb.valid = true) {a b : Qid} (ha : a ∈ kb.items)
    (h : kb.lcsCandidates a b = []) (c : Qid) :
    ¬ (kb.toOntology hv).IsLCS a b c := by
  intro hc
  have := (mem_lcsCandidates_iff hv ha).2 hc
  simp [h] at this

end KB

/-! ## A worked fragment: multiple inheritance without a least common subsumer -/

namespace SubsumptionExample

open Wikidata

/-- animal (Q729). -/
def animal : Qid := .wd "Q729"
/-- bird (Q5113). -/
def bird : Qid := .wd "Q5113"
/-- aquatic animal (Q2374463). -/
def aquatic : Qid := .wd "Q2374463"
/-- duck (Q3736439). -/
def duck : Qid := .wd "Q3736439"
/-- swan (Q39072). -/
def swan : Qid := .wd "Q39072"
/-- Donald Duck (Q16549), an individual duck. -/
def donald : Qid := .wd "Q16549"

/-- Ducks and swans are both birds and both aquatic animals; birds and aquatic
animals are both animals, but neither is a subclass of the other. -/
def frag : KB where
  name := "subsumption fragment"
  items := [animal, bird, aquatic, duck, swan, donald]
  levels := [(animal, 1), (bird, 1), (aquatic, 1), (duck, 1), (swan, 1), (donald, 0)]
  sub := [(bird, animal), (aquatic, animal), (duck, bird), (duck, aquatic),
    (swan, bird), (swan, aquatic)]
  inst := [(donald, duck)]

theorem frag_valid : frag.valid = true := by decide

/-- Ducks and swans have three common superclasses ... -/
theorem frag_commonSupers :
    frag.commonSupers duck swan = [animal, bird, aquatic] := by decide

/-- ... but no least one: `bird` and `aquatic animal` are incomparable. -/
theorem frag_no_lcs : frag.lcsCandidates duck swan = [] := by decide

theorem frag_no_lcs_abstract (c : Qid) : ¬ (frag.toOntology frag_valid).IsLCS duck swan c :=
  KB.not_isLCS_of_lcsCandidates_eq_nil frag_valid (by decide) frag_no_lcs c

/-- A duck and a bird do have a least common subsumer, namely `bird`. -/
theorem frag_lcs_duck_bird : frag.lcs? duck bird = some bird := by decide

theorem frag_lcs_duck_bird_abstract : (frag.toOntology frag_valid).IsLCS duck bird bird :=
  KB.isLCS_of_lcs?_eq_some frag_valid (by decide) frag_lcs_duck_bird

/-- Donald Duck, an instance of `duck`, is therefore an instance of that least
common subsumer. -/
theorem donald_bird :
    (frag.toOntology frag_valid).InstanceOf donald bird :=
  Ontology.instanceOf_isLCS
    ((frag.isInstanceOf_iff_instanceOf frag_valid donald duck).1 (by decide))
    frag_lcs_duck_bird_abstract

/-- An individual and a class have no common superclass, since they sit at
different metaclass levels. -/
theorem no_common_superclass_donald_duck (c : Qid) :
    ¬ (frag.toOntology frag_valid).IsCommonSuperclass donald duck c :=
  Ontology.not_isCommonSuperclass_of_level_ne (by decide)

end SubsumptionExample

end Wikidata
