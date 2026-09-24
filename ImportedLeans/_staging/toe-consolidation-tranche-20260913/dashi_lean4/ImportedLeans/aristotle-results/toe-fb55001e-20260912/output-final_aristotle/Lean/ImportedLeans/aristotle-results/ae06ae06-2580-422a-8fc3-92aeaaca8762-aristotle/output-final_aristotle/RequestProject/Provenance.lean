import RequestProject.Core
import RequestProject.Engine
import RequestProject.Temporal

/-!
# References and provenance

Wikidata's core policy is *verifiability*: a statement should be backed by a
reference.  A reference is a small group of statements attached to a claim, the
most common ones being

* `stated in` (P248) — the work the claim is taken from,
* `reference URL` (P854), and
* `imported from Wikimedia project` (P143), which is explicitly **not** an
  acceptable source, only a provenance note.

This file adds that layer on top of the ontology.

The abstract half restricts an ontology to a selection of its asserted
statements (`Wikidata.Ontology.restrict`) and shows that the selection is again
an ontology, whose derived facts are among the derived facts of the whole; a
derived `subclass of` fact is *supported* by a finite chain of asserted
statements, and it is verifiable exactly when some such chain consists of
referenced statements only.

The executable half attaches reference lists to the `subclass of` and
`instance of` statements of a knowledge base (`Wikidata.RKB`).  Three ordinary
knowledge bases are extracted from it: `full` (everything asserted), `sourced`
(the statements carrying a reference) and `reliable` (the statements carrying a
reference other than `imported from`).  Main results: the three bases form a
chain, each is valid as soon as the full one is, so all ontology theorems apply
to the sourced and to the reliable fragment, and the derived facts increase
along the chain — sourcing can only ever *lose* facts, never invent them.  A
worked fragment exhibits a fact that is asserted but not verifiable, and one
that is verifiable only through an `imported from` reference.
-/

namespace Wikidata

/-! ## The abstract layer: restricting an ontology to selected statements -/

namespace Ontology

variable {I : Type*} (O : Ontology I)

/-- The sub-ontology spanned by a selection `RS` of the `subclass of` statements
and a selection `RI` of the `instance of` statements: the metaclass levels are
unchanged, and all the ontology axioms are inherited. -/
def restrict (RS RI : I → I → Prop) (hS : ∀ {a b}, RS a b → O.P279 a b)
    (hI : ∀ {a c}, RI a c → O.P31 a c) : Ontology I where
  P279 := RS
  P31 := RI
  level := O.level
  level_P31 h := O.level_P31 (hI h)
  level_P279 h := O.level_P279 (hS h)
  P279_isClass h := O.P279_isClass (hS h)
  P279_antisymm h₁ h₂ :=
    O.P279_antisymm (h₁.mono fun _ _ h => hS h) (h₂.mono fun _ _ h => hS h)

variable {O} {RS RI : I → I → Prop} {hS : ∀ {a b}, RS a b → O.P279 a b}
    {hI : ∀ {a c}, RI a c → O.P31 a c}

@[simp] theorem restrict_level : (O.restrict RS RI hS hI).level = O.level := rfl

/-- Facts derived from selected statements are facts of the whole ontology. -/
theorem restrict_subclassOf_le {a b : I} (h : (O.restrict RS RI hS hI).SubclassOf a b) :
    O.SubclassOf a b :=
  h.mono fun _ _ h => hS h

/-- Instances derived from selected statements are instances of the whole
ontology. -/
theorem restrict_instanceOf_le {a c : I} (h : (O.restrict RS RI hS hI).InstanceOf a c) :
    O.InstanceOf a c := by
  obtain ⟨d, hd, hdc⟩ := h
  exact ⟨d, hI hd, restrict_subclassOf_le (hS := hS) (hI := hI) hdc⟩

/-- A larger selection derives more `subclass of` facts. -/
theorem restrict_subclassOf_mono {RS' RI' : I → I → Prop}
    {hS' : ∀ {a b}, RS' a b → O.P279 a b} {hI' : ∀ {a c}, RI' a c → O.P31 a c}
    (h : ∀ {a b}, RS a b → RS' a b) {a b : I}
    (hab : (O.restrict RS RI hS hI).SubclassOf a b) :
    (O.restrict RS' RI' hS' hI').SubclassOf a b :=
  Relation.ReflTransGen.mono (fun _ _ hxy => h hxy) hab

/-- A larger selection derives more `instance of` facts. -/
theorem restrict_instanceOf_mono {RS' RI' : I → I → Prop}
    {hS' : ∀ {a b}, RS' a b → O.P279 a b} {hI' : ∀ {a c}, RI' a c → O.P31 a c}
    (h : ∀ {a b}, RS a b → RS' a b) (h' : ∀ {a c}, RI a c → RI' a c) {a c : I}
    (hac : (O.restrict RS RI hS hI).InstanceOf a c) :
    (O.restrict RS' RI' hS' hI').InstanceOf a c := by
  obtain ⟨d, hd, hdc⟩ := hac
  exact ⟨d, h' hd, restrict_subclassOf_mono (hS := hS) (hI := hI) (hS' := hS') (hI' := hI') h hdc⟩

/-! ### Support: every derived fact rests on a finite chain of statements -/

/-- **Support**: a derived `subclass of` fact is exactly one witnessed by a finite
chain of asserted `subclass of` statements. -/
theorem subclassOf_iff_exists_chain (O : Ontology I) (a b : I) :
    O.SubclassOf a b ↔
      ∃ l : List I, List.IsChain O.P279 (a :: l) ∧
        (a :: l).getLast (List.cons_ne_nil _ _) = b := by
  constructor
  · intro h
    obtain ⟨l, hl, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen h
    exact ⟨l, hl, hlast⟩
  · rintro ⟨l, hl, hlast⟩
    exact List.relationReflTransGen_of_exists_isChain_cons l hl hlast

/-- **Verifiability criterion**: a chain of *referenced* statements makes a
derived fact verifiable, i.e. derivable in the referenced fragment. -/
theorem restrict_subclassOf_of_chain (a b : I) (l : List I)
    (hl : List.IsChain RS (a :: l)) (hlast : (a :: l).getLast (List.cons_ne_nil _ _) = b) :
    (O.restrict RS RI hS hI).SubclassOf a b :=
  List.relationReflTransGen_of_exists_isChain_cons l hl hlast

end Ontology

/-! ## References -/

/-- The kind of a source reference. -/
inductive RefKind where
  /-- `stated in` (P248): the work the claim is taken from. -/
  | statedIn
  /-- `reference URL` (P854). -/
  | referenceURL
  /-- `imported from Wikimedia project` (P143): a provenance note, not a source. -/
  | importedFrom
deriving DecidableEq, Repr, Inhabited

/-- Whether a reference counts as a source on Wikidata: `imported from Wikimedia
project` does not. -/
def RefKind.reliable : RefKind → Bool
  | .importedFrom => false
  | _ => true

/-- A reference attached to a statement. -/
structure Ref where
  /-- Which reference property is used. -/
  kind : RefKind
  /-- The item cited, for `stated in` and `imported from`. -/
  source : Qid := .wd ""
  /-- The URL cited, for `reference URL`. -/
  url : String := ""
deriving DecidableEq, Repr, Inhabited

/-- A statement carries a reference. -/
def hasRef (rs : List Ref) : Bool := !rs.isEmpty

/-- A statement carries a reference that counts as a source. -/
def hasReliableRef (rs : List Ref) : Bool := rs.any (fun r => r.kind.reliable)

theorem hasRef_of_hasReliableRef {rs : List Ref} (h : hasReliableRef rs = true) :
    hasRef rs = true := by
  simp only [hasReliableRef, List.any_eq_true] at h
  obtain ⟨r, hr, -⟩ := h
  simpa [hasRef, List.isEmpty_iff] using List.ne_nil_of_mem hr

/-! ## The executable layer: knowledge bases with references -/

/-- A knowledge base whose `subclass of` and `instance of` statements each carry a
(possibly empty) list of references. -/
structure RKB where
  /-- A human readable name. -/
  name : String := "sourced ontology"
  /-- The items. -/
  items : List Qid
  /-- The metaclass levels. -/
  levels : List (Qid × ℕ) := []
  /-- Referenced `subclass of` (P279) statements. -/
  rsub : List ((Qid × Qid) × List Ref) := []
  /-- Referenced `instance of` (P31) statements. -/
  rinst : List ((Qid × Qid) × List Ref) := []
  /-- Declared disjointness between classes. -/
  disj : List (Qid × Qid) := []
deriving Repr, DecidableEq, Inhabited

namespace KB

variable {kb kb' : KB}

/-- Deleting `subclass of` statements can only lose derived `subclass of` facts. -/
theorem isSubclassOf_mono (hwf : kb.wellFormed = true) (hwf' : kb'.wellFormed = true)
    (hsub : ∀ x ∈ kb'.sub, x ∈ kb.sub) {a b : Qid} (h : kb'.isSubclassOf a b = true) :
    kb.isSubclassOf a b = true := by
  rw [isSubclassOf_iff hwf]
  rw [isSubclassOf_iff hwf'] at h
  exact h.mono fun _ _ hxy => hsub _ hxy

/-- Deleting statements can only lose derived `instance of` facts. -/
theorem isInstanceOf_mono (hwf : kb.wellFormed = true) (hwf' : kb'.wellFormed = true)
    (hsub : ∀ x ∈ kb'.sub, x ∈ kb.sub) (hinst : ∀ x ∈ kb'.inst, x ∈ kb.inst) {a c : Qid}
    (h : kb'.isInstanceOf a c = true) : kb.isInstanceOf a c = true := by
  rw [isInstanceOf_iff hwf]
  rw [isInstanceOf_iff hwf'] at h
  obtain ⟨d, hd, hdc⟩ := h
  exact ⟨d, hinst _ hd, hdc.mono fun _ _ hxy => hsub _ hxy⟩

end KB

namespace RKB

variable (T : RKB)

/-- The ordinary knowledge base of the statements whose reference list passes the
test `p`. -/
def select (p : List Ref → Bool) : KB where
  name := T.name
  items := T.items
  levels := T.levels
  sub := (T.rsub.filter (fun e => p e.2)).map Prod.fst
  inst := (T.rinst.filter (fun e => p e.2)).map Prod.fst
  disj := T.disj

/-- Everything that is asserted, references or not. -/
def full : KB := T.select (fun _ => true)

/-- The fragment of statements carrying at least one reference. -/
def sourced : KB := T.select hasRef

/-- The fragment of statements carrying at least one reference that counts as a
source (so `imported from` alone is not enough). -/
def reliable : KB := T.select hasReliableRef

@[simp] theorem select_items (p : List Ref → Bool) : (T.select p).items = T.items := rfl
@[simp] theorem select_levels (p : List Ref → Bool) : (T.select p).levels = T.levels := rfl
@[simp] theorem select_disj (p : List Ref → Bool) : (T.select p).disj = T.disj := rfl

variable {T}

theorem select_sub_mono {p q : List Ref → Bool} (hpq : ∀ rs, p rs = true → q rs = true)
    {x : Qid × Qid} (h : x ∈ (T.select p).sub) : x ∈ (T.select q).sub := by
  simp only [select, List.mem_map, List.mem_filter] at h ⊢
  obtain ⟨e, ⟨he, hp⟩, hx⟩ := h
  exact ⟨e, ⟨he, hpq _ hp⟩, hx⟩

theorem select_inst_mono {p q : List Ref → Bool} (hpq : ∀ rs, p rs = true → q rs = true)
    {x : Qid × Qid} (h : x ∈ (T.select p).inst) : x ∈ (T.select q).inst := by
  simp only [select, List.mem_map, List.mem_filter] at h ⊢
  obtain ⟨e, ⟨he, hp⟩, hx⟩ := h
  exact ⟨e, ⟨he, hpq _ hp⟩, hx⟩

theorem sub_of_mem_sourced_sub {x : Qid × Qid} (h : x ∈ T.sourced.sub) : x ∈ T.full.sub :=
  select_sub_mono (fun _ _ => rfl) h

theorem inst_of_mem_sourced_inst {x : Qid × Qid} (h : x ∈ T.sourced.inst) : x ∈ T.full.inst :=
  select_inst_mono (fun _ _ => rfl) h

theorem sub_of_mem_reliable_sub {x : Qid × Qid} (h : x ∈ T.reliable.sub) : x ∈ T.sourced.sub :=
  select_sub_mono (fun _ h => hasRef_of_hasReliableRef h) h

theorem inst_of_mem_reliable_inst {x : Qid × Qid} (h : x ∈ T.reliable.inst) : x ∈ T.sourced.inst :=
  select_inst_mono (fun _ h => hasRef_of_hasReliableRef h) h

/-- **Selecting statements preserves validity**: if the whole base is valid, so is
the fragment cut out by any reference test — hence all the theorems of
`RequestProject.Core` hold of the sourced and of the reliable fragment. -/
theorem valid_select {p : List Ref → Bool} (hv : T.full.valid = true) :
    (T.select p).valid = true :=
  KB.valid_of_subset (kb := T.full) (kb' := T.select p) rfl rfl
    (fun _ h => select_sub_mono (fun _ _ => rfl) h)
    (fun _ h => select_inst_mono (fun _ _ => rfl) h) (fun _ h => h) hv

theorem valid_sourced (hv : T.full.valid = true) : T.sourced.valid = true := valid_select hv

theorem valid_reliable (hv : T.full.valid = true) : T.reliable.valid = true := valid_select hv

/-- **Sourcing never invents facts**: a verifiable `subclass of` fact is an
asserted-and-derived one. -/
theorem isSubclassOf_sourced_le (hv : T.full.valid = true) {a b : Qid}
    (h : T.sourced.isSubclassOf a b = true) : T.full.isSubclassOf a b = true :=
  KB.isSubclassOf_mono (KB.valid_wellFormed hv) (KB.valid_wellFormed (valid_sourced hv))
    (fun _ h => sub_of_mem_sourced_sub h) h

/-- **Sourcing never invents facts**, for `instance of`. -/
theorem isInstanceOf_sourced_le (hv : T.full.valid = true) {a c : Qid}
    (h : T.sourced.isInstanceOf a c = true) : T.full.isInstanceOf a c = true :=
  KB.isInstanceOf_mono (KB.valid_wellFormed hv) (KB.valid_wellFormed (valid_sourced hv))
    (fun _ h => sub_of_mem_sourced_sub h) (fun _ h => inst_of_mem_sourced_inst h) h

/-- A fact resting on reliable references is in particular verifiable. -/
theorem isSubclassOf_reliable_le (hv : T.full.valid = true) {a b : Qid}
    (h : T.reliable.isSubclassOf a b = true) : T.sourced.isSubclassOf a b = true :=
  KB.isSubclassOf_mono (KB.valid_wellFormed (valid_sourced hv))
    (KB.valid_wellFormed (valid_reliable hv)) (fun _ h => sub_of_mem_reliable_sub h) h

/-- A fact resting on reliable references is in particular verifiable, for
`instance of`. -/
theorem isInstanceOf_reliable_le (hv : T.full.valid = true) {a c : Qid}
    (h : T.reliable.isInstanceOf a c = true) : T.sourced.isInstanceOf a c = true :=
  KB.isInstanceOf_mono (KB.valid_wellFormed (valid_sourced hv))
    (KB.valid_wellFormed (valid_reliable hv)) (fun _ h => sub_of_mem_reliable_sub h)
    (fun _ h => inst_of_mem_reliable_inst h) h

variable (T)

/-- The verifiable derived `subclass of` facts: those derivable from referenced
statements alone. -/
def verifiableSubclass (a b : Qid) : Bool := T.sourced.isSubclassOf a b

/-- The verifiable derived `instance of` facts. -/
def verifiableInstance (a c : Qid) : Bool := T.sourced.isInstanceOf a c

/-- The asserted statements of the base that carry no reference at all. -/
def unsourcedStatements : List (Qid × Qid) :=
  (T.rsub.filter (fun e => !hasRef e.2)).map Prod.fst ++
    (T.rinst.filter (fun e => !hasRef e.2)).map Prod.fst

/-- Every statement is either sourced or listed as unsourced. -/
theorem mem_sourced_or_unsourced {x : Qid × Qid} (h : x ∈ T.full.sub) :
    x ∈ T.sourced.sub ∨ x ∈ T.unsourcedStatements := by
  simp only [full, select, List.mem_map, List.mem_filter] at h
  obtain ⟨e, ⟨he, -⟩, hx⟩ := h
  by_cases hr : hasRef e.2 = true
  · refine Or.inl ?_
    simp only [sourced, select, List.mem_map, List.mem_filter]
    exact ⟨e, ⟨he, hr⟩, hx⟩
  · refine Or.inr ?_
    simp only [unsourcedStatements, List.mem_append, List.mem_map, List.mem_filter]
    exact Or.inl ⟨e, ⟨he, by simp [hr]⟩, hx⟩

end RKB

/-! ## A worked fragment

Three `subclass of` statements and two `instance of` statements, with references
of the three kinds; one statement is unsourced and one rests only on an
`imported from` note. -/

namespace ProvenanceExample

open Wikidata

/-- Douglas Adams (Q42). -/
def adams : Qid := .wd "Q42"
/-- human (Q5). -/
def human : Qid := .wd "Q5"
/-- person (Q215627). -/
def person : Qid := .wd "Q215627"
/-- omnivore (Q164509), here used as a class of individuals. -/
def omnivore : Qid := .wd "Q164509"
/-- The English Wikipedia (Q328), a provenance note but not a source. -/
def enwiki : Qid := .wd "Q328"
/-- *Integrated Authority File* (Q36578), a reference work. -/
def gnd : Qid := .wd "Q36578"

/-- A `stated in` reference to the Integrated Authority File. -/
def refGnd : Ref := { kind := .statedIn, source := gnd }

/-- A `reference URL`. -/
def refUrl : Ref := { kind := .referenceURL, url := "https://example.org/adams" }

/-- An `imported from Wikimedia project` note, which is not a source. -/
def refImported : Ref := { kind := .importedFrom, source := enwiki }

/-- The fragment: `human ⊑ person`, referenced; `omnivore ⊑ person`, unreferenced;
Adams an instance of `human`, referenced; Adams an instance of `omnivore`, only
imported from Wikipedia. -/
def frag : RKB where
  name := "provenance fragment"
  items := [adams, human, person, omnivore]
  levels := [(adams, 0), (human, 1), (person, 1), (omnivore, 1)]
  rsub := [((human, person), [refGnd]), ((omnivore, person), [])]
  rinst := [((adams, human), [refUrl, refImported]), ((adams, omnivore), [refImported])]

/-- The whole fragment is a valid ontology. -/
theorem frag_valid : frag.full.valid = true := by decide

/-- Hence so are its sourced and reliable fragments. -/
theorem frag_sourced_valid : frag.sourced.valid = true := RKB.valid_sourced frag_valid

theorem frag_reliable_valid : frag.reliable.valid = true := RKB.valid_reliable frag_valid

/-- Adams is derived to be a person. -/
theorem adams_person : frag.full.isInstanceOf adams person = true := by decide

/-- And verifiably so: the derivation uses only referenced statements. -/
theorem adams_person_verifiable : frag.verifiableInstance adams person = true := by decide

/-- Adams is derived to be an omnivore, ... -/
theorem adams_omnivore : frag.full.isInstanceOf adams omnivore = true := by decide

/-- ... verifiably, since the statement carries an `imported from` reference, ... -/
theorem adams_omnivore_verifiable : frag.verifiableInstance adams omnivore = true := by decide

/-- ... but not reliably: `imported from Wikimedia project` is not a source. -/
theorem adams_omnivore_not_reliable :
    frag.reliable.isInstanceOf adams omnivore = false := by decide

/-- The `subclass of` statement `omnivore ⊑ person` carries no reference at all,
so it is reported as unsourced ... -/
theorem omnivore_person_unsourced : (omnivore, person) ∈ frag.unsourcedStatements := by decide

/-- ... and the derived fact that omnivores are persons is not verifiable. -/
theorem omnivore_person_not_verifiable : frag.verifiableSubclass omnivore person = false := by
  decide

/-- The unsourced fact is nevertheless asserted in the full base. -/
theorem omnivore_person_asserted : frag.full.isSubclassOf omnivore person = true := by decide

end ProvenanceExample

end Wikidata
