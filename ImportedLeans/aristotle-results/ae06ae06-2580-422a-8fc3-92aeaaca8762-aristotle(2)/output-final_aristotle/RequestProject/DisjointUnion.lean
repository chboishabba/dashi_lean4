import RequestProject.Engine

/-!
# `disjoint union of` (P2738)

Wikidata's property `disjoint union of` (P2738) says that a class is exactly carved up
by a list of subclasses: each listed class is a subclass of it, no two of them share an
instance, and every instance of the class is an instance of one of them.  It is the
strongest of the ontology-layer statements about a class — a genuine *partition* of the
class extension — and it is what licenses reasoning by cases about the instances of the
class.

This file adds that layer to the development:

* `Wikidata.Ontology.IsDisjointUnion O c Part` is the abstract statement, phrased with
  the *derived* `subclass of` and `instance of` relations of `RequestProject.Core`;
* `Wikidata.Ontology.WithDisjointness.isDisjointUnion_of_declared` derives it from
  declared disjointness (P1889-style `disjoint with` statements) plus coverage;
* the consequences: every instance lies in exactly one part
  (`Wikidata.Ontology.IsDisjointUnion.existsUnique_part`), the class is empty when all
  the parts are (`...not_hasInstance`), a part that exhausts the class leaves the other
  parts empty (`...not_hasInstance_of_part_eq`), and partitions *compose*: refining
  every part of a partition again yields a partition
  (`Wikidata.Ontology.IsDisjointUnion.comp`);
* an executable checker `Wikidata.KB.dunOk` on a finite knowledge base, proved sound:
  a knowledge base passing it really is partitioned in the abstract sense
  (`Wikidata.KB.isDisjointUnion_of_dunOk`);
* a worked fragment, where the partition of a class is checked, used to reason by
  cases, and where a knowledge base with a missing case and one with an overlap are
  both rejected.

As elsewhere in this development the identifiers follow Wikidata, but the fragment is a
stylised excerpt; the theorems about it are statements about that fragment.
-/

namespace Wikidata

namespace Ontology

variable {I : Type*} {O : Ontology I}

/-- `IsDisjointUnion O c Part`: the class `c` is the disjoint union (P2738) of the
classes satisfying `Part`.  Disjointness is stated extensionally — no item is an
instance of two different parts — so that the notion is stable under refinement. -/
structure IsDisjointUnion (O : Ontology I) (c : I) (Part : I → Prop) : Prop where
  /-- Every part is a subclass of the whole. -/
  subclass : ∀ ⦃p⦄, Part p → O.SubclassOf p c
  /-- Two different parts share no instance. -/
  disjoint : ∀ ⦃p q a⦄, Part p → Part q → p ≠ q → O.InstanceOf a p → ¬ O.InstanceOf a q
  /-- Every instance of the whole is an instance of some part. -/
  cover : ∀ ⦃a⦄, O.InstanceOf a c → ∃ p, Part p ∧ O.InstanceOf a p

namespace IsDisjointUnion

variable {c : I} {Part : I → Prop} (h : IsDisjointUnion O c Part)
include h

/-- An instance of a part is an instance of the whole. -/
theorem instanceOf_of_part {a p : I} (hp : Part p) (ha : O.InstanceOf a p) :
    O.InstanceOf a c :=
  instanceOf_trans_subclassOf ha (h.subclass hp)

/-- The instances of the whole are exactly the instances of the parts. -/
theorem instanceOf_iff {a : I} : O.InstanceOf a c ↔ ∃ p, Part p ∧ O.InstanceOf a p :=
  ⟨fun ha => h.cover ha, fun ⟨_, hp, ha⟩ => h.instanceOf_of_part hp ha⟩

/-- **Reasoning by cases.** Every instance of the whole lies in exactly one part. -/
theorem existsUnique_part {a : I} (ha : O.InstanceOf a c) :
    ∃! p, Part p ∧ O.InstanceOf a p := by
  obtain ⟨p, hp, hap⟩ := h.cover ha
  refine ⟨p, ⟨hp, hap⟩, ?_⟩
  rintro q ⟨hq, haq⟩
  by_contra hne
  exact h.disjoint hq hp hne haq hap

/-- If no part has an instance, neither has the whole. -/
theorem not_hasInstance (hempty : ∀ ⦃p⦄, Part p → ¬ O.HasInstance p) : ¬ O.HasInstance c := by
  rintro ⟨a, ha⟩
  obtain ⟨p, hp, hap⟩ := h.cover ha
  exact hempty hp ⟨a, hap⟩

/-- A part that is the whole class leaves every other part empty. -/
theorem not_hasInstance_of_part_eq {p q : I} (hp : Part p) (hq : Part q) (hpc : p = c)
    (hne : q ≠ p) : ¬ O.HasInstance q := by
  rintro ⟨a, ha⟩
  have hac : O.InstanceOf a c := h.instanceOf_of_part hq ha
  exact h.disjoint hq hp hne ha (hpc ▸ hac)

/-- A subclass of the whole that meets no part has no instances. -/
theorem not_hasInstance_of_avoids_parts {d : I} (hd : O.SubclassOf d c)
    (havoid : ∀ ⦃p a⦄, Part p → O.InstanceOf a d → ¬ O.InstanceOf a p) : ¬ O.HasInstance d := by
  rintro ⟨a, ha⟩
  obtain ⟨p, hp, hap⟩ := h.cover (instanceOf_trans_subclassOf ha hd)
  exact havoid hp ha hap

/-- Two parts with a common instance are equal. -/
theorem eq_of_common_instance {p q a : I} (hp : Part p) (hq : Part q)
    (hap : O.InstanceOf a p) (haq : O.InstanceOf a q) : p = q := by
  by_contra hne
  exact h.disjoint hp hq hne hap haq

end IsDisjointUnion

/-- **Partitions compose.** If `c` is the disjoint union of the parts `Part`, and each
part `p` is in turn the disjoint union of `Sub p`, then `c` is the disjoint union of all
the sub-parts. -/
theorem IsDisjointUnion.comp {c : I} {Part : I → Prop} {Sub : I → I → Prop}
    (h : IsDisjointUnion O c Part) (hsub : ∀ ⦃p⦄, Part p → IsDisjointUnion O p (Sub p)) :
    IsDisjointUnion O c (fun x => ∃ p, Part p ∧ Sub p x) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro x ⟨p, hp, hx⟩
    exact subclassOf_trans ((hsub hp).subclass hx) (h.subclass hp)
  · rintro x y a ⟨p, hp, hx⟩ ⟨q, hq, hy⟩ hxy hax hay
    have hap : O.InstanceOf a p := (hsub hp).instanceOf_of_part hx hax
    have haq : O.InstanceOf a q := (hsub hq).instanceOf_of_part hy hay
    by_cases hpq : p = q
    · subst hpq
      exact (hsub hp).disjoint hx hy hxy hax hay
    · exact h.disjoint hp hq hpq hap haq
  · intro a ha
    obtain ⟨p, hp, hap⟩ := h.cover ha
    obtain ⟨x, hx, hax⟩ := (hsub hp).cover hap
    exact ⟨x, ⟨p, hp, hx⟩, hax⟩

namespace WithDisjointness

variable {I : Type*} {D : WithDisjointness I}

/-- Declared disjointness (together with coverage) yields a disjoint union: this is the
usual way a P2738 statement is justified on Wikidata, by `disjoint with` statements
between the parts. -/
theorem isDisjointUnion_of_declared {c : I} {Part : I → Prop}
    (hsub : ∀ ⦃p⦄, Part p → D.toOntology.SubclassOf p c)
    (hdisj : ∀ ⦃p q⦄, Part p → Part q → p ≠ q → D.DisjointWith p q)
    (hcover : ∀ ⦃a⦄, D.toOntology.InstanceOf a c → ∃ p, Part p ∧ D.toOntology.InstanceOf a p) :
    IsDisjointUnion D.toOntology c Part where
  subclass := hsub
  disjoint := by
    intro p q a hp hq hne hap haq
    exact D.disjointWith_spec (hdisj hp hq hne) hap haq
  cover := hcover

end WithDisjointness

end Ontology

/-! ### The executable checker -/

namespace KB

variable (kb : KB)

/-- Every listed part is a subclass of the whole. -/
def dunSubclassOk (c : Qid) (ps : List Qid) : Bool :=
  ps.all (fun p => kb.isSubclassOf p c)

/-- No item is an instance of two different listed parts. -/
def dunDisjointOk (ps : List Qid) : Bool :=
  ps.all fun p => ps.all fun q =>
    (p == q) || kb.items.all fun a => !(kb.isInstanceOf a p && kb.isInstanceOf a q)

/-- Every instance of the whole is an instance of a listed part. -/
def dunCoverOk (c : Qid) (ps : List Qid) : Bool :=
  (kb.instancesOf c).all fun a => ps.any fun p => kb.isInstanceOf a p

/-- The `disjoint union of` (P2738) check: the listed classes partition the class. -/
def dunOk (c : Qid) (ps : List Qid) : Bool :=
  kb.dunSubclassOk c ps && kb.dunDisjointOk ps && kb.dunCoverOk c ps

variable {kb}

/-- Any instance (in the derived sense) of any class is an item of a well-formed
knowledge base. -/
theorem mem_items_of_instanceOf (hv : kb.valid = true) {a c : Qid}
    (h : (kb.toOntology hv).InstanceOf a c) : a ∈ kb.items := by
  obtain ⟨d, hd, -⟩ := h
  exact (inst_mem_items (valid_wellFormed hv) hd).1

/-- **Soundness of the checker.** A knowledge base passing `dunOk c ps` really has `c`
partitioned by the classes `ps` in the abstract ontology. -/
theorem isDisjointUnion_of_dunOk (hv : kb.valid = true) {c : Qid} {ps : List Qid}
    (h : kb.dunOk c ps = true) :
    Ontology.IsDisjointUnion (kb.toOntology hv) c (fun p => p ∈ ps) := by
  simp only [dunOk, Bool.and_eq_true] at h
  obtain ⟨⟨hsub, hdisj⟩, hcov⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    exact (isSubclassOf_iff_subclassOf hv p c).1 (List.all_eq_true.1 hsub p hp)
  · intro p q a hp hq hne hap haq
    have hpq := List.all_eq_true.1 (List.all_eq_true.1 hdisj p hp) q hq
    have hne' : (p == q) = false := by
      simpa using hne
    rw [hne', Bool.false_or] at hpq
    have ha : a ∈ kb.items := mem_items_of_instanceOf hv hap
    have := List.all_eq_true.1 hpq a ha
    have e1 : kb.isInstanceOf a p = true := (isInstanceOf_iff_instanceOf hv a p).2 hap
    have e2 : kb.isInstanceOf a q = true := (isInstanceOf_iff_instanceOf hv a q).2 haq
    simp [e1, e2] at this
  · intro a ha
    have hmem : a ∈ kb.instancesOf c :=
      mem_instancesOf.2 ⟨mem_items_of_instanceOf hv ha,
        (isInstanceOf_iff_instanceOf hv a c).2 ha⟩
    obtain ⟨p, hp, hap⟩ := List.any_eq_true.1 (List.all_eq_true.1 hcov a hmem)
    exact ⟨p, hp, (isInstanceOf_iff_instanceOf hv a p).1 hap⟩

end KB

/-! ### A worked fragment -/

namespace DisjointUnionExample

open KB

/-- Abbreviation for a Wikidata item. -/
def Q (s : String) : Qid := .wd s

/-- English labels for the identifiers used below. -/
def labels : List (Qid × String) :=
  [(Q "Q729", "animal"), (Q "Q25241", "vertebrate"), (Q "Q1082709", "invertebrate"),
   (Q "Q140", "lion"), (Q "Q25326", "octopus"), (Q "Q35120", "entity")]

/-- The label of an identifier, or its raw form if none is recorded. -/
def labelOf (q : Qid) : String := (labels.lookup q).getD (toString (repr q))

/-- `animal` is split into `vertebrate` and `invertebrate`, with one instance of each. -/
def animalKB : KB where
  name := "wd-disjoint-union"
  items := [Q "Q729", Q "Q25241", Q "Q1082709", Q "Q140", Q "Q25326", Q "Q35120"]
  levels := [(Q "Q729", 1), (Q "Q25241", 1), (Q "Q1082709", 1), (Q "Q140", 0),
             (Q "Q25326", 0), (Q "Q35120", 1)]
  sub := [(Q "Q25241", Q "Q729"), (Q "Q1082709", Q "Q729"), (Q "Q729", Q "Q35120")]
  inst := [(Q "Q140", Q "Q25241"), (Q "Q25326", Q "Q1082709")]
  disj := [(Q "Q25241", Q "Q1082709")]

set_option maxRecDepth 40000 in
theorem animalKB_valid : animalKB.valid = true := by decide

set_option maxRecDepth 40000 in
/-- The partition passes the `disjoint union of` check. -/
theorem animalKB_dunOk :
    animalKB.dunOk (Q "Q729") [Q "Q25241", Q "Q1082709"] = true := by decide

/-- Hence `animal` really is partitioned by `vertebrate` and `invertebrate` in the
abstract ontology. -/
theorem animalKB_isDisjointUnion :
    Ontology.IsDisjointUnion (animalKB.toOntology animalKB_valid) (Q "Q729")
      (fun p => p ∈ [Q "Q25241", Q "Q1082709"]) :=
  KB.isDisjointUnion_of_dunOk animalKB_valid animalKB_dunOk

/-- Reasoning by cases over the partition: every animal is a vertebrate or an
invertebrate, and never both. -/
theorem animal_cases {a : Qid}
    (ha : (animalKB.toOntology animalKB_valid).InstanceOf a (Q "Q729")) :
    ((animalKB.toOntology animalKB_valid).InstanceOf a (Q "Q25241") ∧
      ¬ (animalKB.toOntology animalKB_valid).InstanceOf a (Q "Q1082709")) ∨
    ((animalKB.toOntology animalKB_valid).InstanceOf a (Q "Q1082709") ∧
      ¬ (animalKB.toOntology animalKB_valid).InstanceOf a (Q "Q25241")) := by
  obtain ⟨p, hp, hap⟩ := animalKB_isDisjointUnion.cover ha
  have hne : Q "Q25241" ≠ Q "Q1082709" := by decide
  rcases List.mem_cons.1 hp with rfl | hp
  · exact Or.inl ⟨hap, animalKB_isDisjointUnion.disjoint (by simp) (by simp) hne hap⟩
  · have : p = Q "Q1082709" := by simpa using hp
    subst this
    exact Or.inr ⟨hap, animalKB_isDisjointUnion.disjoint (by simp) (by simp) hne.symm hap⟩

set_option maxRecDepth 40000 in
/-- A single part does not exhaust the class: the check fails because the octopus is
not covered. -/
theorem animalKB_dunOk_missing_case :
    animalKB.dunOk (Q "Q729") [Q "Q25241"] = false := by decide

/-- The same fragment with the octopus wrongly also declared a vertebrate. -/
def overlapKB : KB :=
  { animalKB with
    name := "wd-disjoint-union-overlap"
    inst := animalKB.inst ++ [(Q "Q25326", Q "Q25241")]
    disj := [] }

set_option maxRecDepth 40000 in
/-- It is still a valid knowledge base (the disjointness declaration was dropped) — but
the partition check rejects it, because the two parts now overlap. -/
theorem overlapKB_valid : overlapKB.valid = true := by decide

set_option maxRecDepth 40000 in
theorem overlapKB_dunOk_false :
    overlapKB.dunOk (Q "Q729") [Q "Q25241", Q "Q1082709"] = false := by decide

end DisjointUnionExample

end Wikidata
