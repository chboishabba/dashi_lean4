import RequestProject.Merge

/-!
# `equivalent class` (P1709): aligning an ontology with another one

Wikidata does not live alone: `equivalent class` (P1709) and `equivalent property`
(P1628) link its classes and properties to those of external ontologies, and the point
of such a link is that reasoning may be transported along it.  This file formalises
what a link has to satisfy for that to be sound, and what follows once it does.

An `Wikidata.Ontology.Alignment O₁ O₂` is a map on items sending every *asserted*
statement of `O₁` (`subclass of`, `instance of`) to a *derived* fact of `O₂`.  The main
results are:

* `Wikidata.Ontology.Alignment.subclassOf` and
  `Wikidata.Ontology.Alignment.instanceOf` — the derived relations transfer, not just
  the asserted ones;
* `Wikidata.Ontology.Alignment.hasInstance`, `...isClass`, `...isMetaclass` — the
  ontological status of a class transfers with it;
* `Wikidata.Ontology.Alignment.id` and `Wikidata.Ontology.Alignment.comp` — alignments
  form a category, so chains of `equivalent class` links compose;
* `Wikidata.Ontology.Alignment.subclassOf_iff` — a *conservative* alignment (one that
  reflects the class hierarchy) transports the hierarchy exactly, in both directions;
* `Wikidata.Ontology.Alignment.no_common_instance_of_disjoint` — disjointness can be
  *imported* from the external ontology along an instance-reflecting alignment: two
  classes whose images are declared disjoint there share no instance here;
* `Wikidata.KB.alignment_of_alignOk` — the executable checker: a finite table of
  `equivalent class` links between two validated knowledge bases, checked
  statement-by-statement, yields an alignment in the abstract sense.

As elsewhere in this development the identifiers follow Wikidata, but the fragment at
the end is a stylised excerpt; the theorems about it are statements about it.
-/

namespace Wikidata

namespace Ontology

variable {I J K : Type*}

/-- An alignment of `O₁` into `O₂` — an `equivalent class` (P1709) mapping that is
sound: every asserted statement of `O₁` becomes a derived fact of `O₂`. -/
structure Alignment (O₁ : Ontology I) (O₂ : Ontology J) where
  /-- The map on items given by the `equivalent class` links. -/
  map : I → J
  /-- Asserted `subclass of` statements are mapped into the derived hierarchy. -/
  map_P279 : ∀ {a b}, O₁.P279 a b → O₂.SubclassOf (map a) (map b)
  /-- Asserted `instance of` statements are mapped into the derived instance relation. -/
  map_P31 : ∀ {a c}, O₁.P31 a c → O₂.InstanceOf (map a) (map c)

namespace Alignment

variable {O₁ : Ontology I} {O₂ : Ontology J} {O₃ : Ontology K} (F : Alignment O₁ O₂)
include F

/-- The *derived* class hierarchy transfers along an alignment. -/
theorem subclassOf {a b : I} (h : O₁.SubclassOf a b) : O₂.SubclassOf (F.map a) (F.map b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact subclassOf_trans ih (F.map_P279 hbc)

/-- The *derived* instance relation transfers along an alignment. -/
theorem instanceOf {a c : I} (h : O₁.InstanceOf a c) : O₂.InstanceOf (F.map a) (F.map c) := by
  obtain ⟨d, hd, hdc⟩ := h
  exact instanceOf_trans_subclassOf (F.map_P31 hd) (F.subclassOf hdc)

/-- A class with instances is mapped to a class with instances. -/
theorem hasInstance {c : I} (h : O₁.HasInstance c) : O₂.HasInstance (F.map c) := by
  obtain ⟨a, ha⟩ := h
  exact ⟨F.map a, F.instanceOf ha⟩

/-- A class is mapped to a class. -/
theorem isClass {c : I} (h : O₁.HasInstance c) : O₂.IsClass (F.map c) :=
  isClass_of_hasInstance (F.hasInstance h)

/-- A metaclass is mapped to a metaclass. -/
theorem isMetaclass {c : I} (h : O₁.IsMetaclass c) : O₂.IsMetaclass (F.map c) := by
  obtain ⟨a, hac, ha⟩ := h
  exact ⟨F.map a, F.instanceOf hac, F.hasInstance ha⟩

/-- Along an alignment an instance still sits one level below its class, even though
the absolute levels of the two ontologies need not agree. -/
theorem level_step {a c : I} (h : O₁.InstanceOf a c) :
    O₂.level (F.map c) = O₂.level (F.map a) + 1 :=
  level_instanceOf (F.instanceOf h)

omit F

/-- Every ontology is aligned with itself. -/
def id (O : Ontology I) : Alignment O O where
  map := _root_.id
  map_P279 h := subclassOf_of_P279 h
  map_P31 h := instanceOf_of_P31 h

/-- Alignments compose: a chain of `equivalent class` links is an alignment. -/
def comp (F : Alignment O₁ O₂) (G : Alignment O₂ O₃) : Alignment O₁ O₃ where
  map := G.map ∘ F.map
  map_P279 h := G.subclassOf (F.map_P279 h)
  map_P31 h := G.instanceOf (F.map_P31 h)

@[simp] theorem comp_map (F : Alignment O₁ O₂) (G : Alignment O₂ O₃) :
    (F.comp G).map = G.map ∘ F.map := rfl

@[simp] theorem id_map (O : Ontology I) : (Alignment.id O).map = _root_.id := rfl

/-- A **conservative** alignment transports the class hierarchy exactly: it adds no
subclass facts that were not there already. -/
theorem subclassOf_iff (F : Alignment O₁ O₂)
    (hrefl : ∀ {a b : I}, O₂.SubclassOf (F.map a) (F.map b) → O₁.SubclassOf a b) {a b : I} :
    O₂.SubclassOf (F.map a) (F.map b) ↔ O₁.SubclassOf a b :=
  ⟨hrefl, F.subclassOf⟩

/-- **Importing disjointness.** If the images of two classes are declared disjoint in
the external ontology, and the alignment reflects instances, then the two classes share
no instance here either. -/
theorem no_common_instance_of_disjoint {D : WithDisjointness J} (F : Alignment O₁ D.toOntology)
    {c d a : I} (hdisj : D.DisjointWith (F.map c) (F.map d))
    (hc : O₁.InstanceOf a c) (hd : O₁.InstanceOf a d) : False :=
  D.disjointWith_spec hdisj (F.instanceOf hc) (F.instanceOf hd)

end Alignment

end Ontology

/-! ### The executable alignment checker -/

namespace KB

/-- The item map given by a finite table of `equivalent class` (P1709) links; an
identifier with no link is kept as it is. -/
def applyMap (m : List (Qid × Qid)) (q : Qid) : Qid := (m.lookup q).getD q

/-- The alignment check: every asserted statement of `kb` must be a derived fact of the
target knowledge base after applying the link table. -/
def alignOk (kb kb' : KB) (m : List (Qid × Qid)) : Bool :=
  kb.sub.all (fun pr => kb'.isSubclassOf (applyMap m pr.1) (applyMap m pr.2)) &&
  kb.inst.all (fun pr => kb'.isInstanceOf (applyMap m pr.1) (applyMap m pr.2))

/-- **Soundness of the alignment checker.** A checked link table between two validated
knowledge bases is an alignment of the abstract ontologies, so every transfer theorem
above applies to it. -/
def alignment_of_alignOk {kb kb' : KB} (hv : kb.valid = true) (hv' : kb'.valid = true)
    (m : List (Qid × Qid)) (h : kb.alignOk kb' m = true) :
    Ontology.Alignment (kb.toOntology hv) (kb'.toOntology hv') where
  map := applyMap m
  map_P279 := by
    intro a b hab
    have h' := (Bool.and_eq_true _ _).mp h
    have := List.all_eq_true.1 h'.1 (a, b) hab
    exact (isSubclassOf_iff_subclassOf hv' _ _).1 this
  map_P31 := by
    intro a c hac
    have h' := (Bool.and_eq_true _ _).mp h
    have := List.all_eq_true.1 h'.2 (a, c) hac
    exact (isInstanceOf_iff_instanceOf hv' _ _).1 this

end KB

/-! ### A worked fragment -/

namespace AlignmentExample

open KB

/-- Abbreviation for a Wikidata item. -/
def Q (s : String) : Qid := .wd s

/-- A small Wikidata fragment: the lion (Q140) is an instance of the class `taxon`
(Q16521), itself a subclass of `entity` (Q35120). -/
def wdFragment : KB where
  name := "wd-fragment"
  items := [Q "Q140", Q "Q16521", Q "Q35120"]
  levels := [(Q "Q140", 0), (Q "Q16521", 1), (Q "Q35120", 1)]
  sub := [(Q "Q16521", Q "Q35120")]
  inst := [(Q "Q140", Q "Q16521")]

set_option maxRecDepth 40000 in
theorem wdFragment_valid : wdFragment.valid = true := by decide

/-- An external ontology, with its own identifiers, in which the lion is an instance of
`mammal`, a subclass of `animal`, a subclass of its own top class. -/
def extOntology : KB where
  name := "external"
  items := [Q "E-lion", Q "E-mammal", Q "E-animal", Q "E-thing"]
  levels := [(Q "E-lion", 0), (Q "E-mammal", 1), (Q "E-animal", 1), (Q "E-thing", 1)]
  sub := [(Q "E-mammal", Q "E-animal"), (Q "E-animal", Q "E-thing")]
  inst := [(Q "E-lion", Q "E-mammal")]

set_option maxRecDepth 40000 in
theorem extOntology_valid : extOntology.valid = true := by decide

/-- The `equivalent class` table: taxon ↦ animal, entity ↦ thing, lion ↦ lion. -/
def links : List (Qid × Qid) :=
  [(Q "Q140", Q "E-lion"), (Q "Q16521", Q "E-animal"), (Q "Q35120", Q "E-thing")]

set_option maxRecDepth 40000 in
/-- The links pass the alignment check: every asserted statement of the Wikidata
fragment is derivable in the external ontology after mapping. -/
theorem links_alignOk : wdFragment.alignOk extOntology links = true := by decide

/-- Hence they are an alignment in the abstract sense. -/
noncomputable def alignment :
    Ontology.Alignment (wdFragment.toOntology wdFragment_valid)
      (extOntology.toOntology extOntology_valid) :=
  KB.alignment_of_alignOk wdFragment_valid extOntology_valid links links_alignOk

/-- Transport along the alignment: because the lion is (derivably) an instance of
`entity` here, its image is an instance of the external top class there. -/
theorem lion_instanceOf_thing :
    (extOntology.toOntology extOntology_valid).InstanceOf (Q "E-lion") (Q "E-thing") := by
  have h : (wdFragment.toOntology wdFragment_valid).InstanceOf (Q "Q140") (Q "Q35120") :=
    (isInstanceOf_iff_instanceOf wdFragment_valid _ _).1 (by decide)
  have := alignment.instanceOf h
  simpa [alignment, KB.alignment_of_alignOk, applyMap, links] using this

set_option maxRecDepth 40000 in
/-- A link table that maps the two classes the wrong way round is rejected. -/
theorem bad_links_alignOk_false :
    wdFragment.alignOk extOntology
      [(Q "Q140", Q "E-lion"), (Q "Q16521", Q "E-thing"), (Q "Q35120", Q "E-animal")]
      = false := by decide

end AlignmentExample

end Wikidata
