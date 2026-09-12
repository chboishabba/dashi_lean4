import RequestProject.Generated.Theories
import RequestProject.Vocabulary
import RequestProject.HomotopyTypes
import RequestProject.GrothendieckSite

/-!
# What Wikidata says about topology, category theory, and the rest

`RequestProject.MathCorpus` closes the loop for the mathematics the *core* of the
development is made of.  This file does the same for the theories that
`RequestProject.CategoryOfOntologies`, `OntologyTopology`, `GrothendieckSite`,
`HomotopyTypes`, `CubicalTypes`, `OntologyGroups` and `OntologyFields` add on top
of the pullback: the fragment `RequestProject.Generated.Theories` was downloaded
from the live Wikidata API with exactly those articles as its seeds, so what
Wikidata says about *topology*, *Grothendieck topology*, *homotopy type theory*,
*cubical type theory*, *category theory*, *field theory* and *group theory* is
itself an ontology this library can check.

Three things are proved.

* `theoryArticles_are_items` — every article is an item of the downloaded
  fragment;
* `theoryArticles_are_grounded` — every one of them is matched, in
  `Wikidata.vocabulary`, with a declaration of this development;
* a list of *agreements*: a `subclass of` fact Wikidata asserts about those
  notions, next to the construction of this library that instantiates it.
  Wikidata says a group is a monoid; here the automorphisms of an ontology
  (`Ontology.autPerm`) are the invertible part of the monoid of its
  endomorphisms (`Ontology.endoSubmonoid`).  Wikidata says a field is a vector
  space and a vector space is a free module; here class extensions over `GF(2)`
  are exactly that (`Ontology.ExtSpace`).  Wikidata says an Alexandrov topology
  is a topology; here the class hierarchy of an ontology carries one
  (`Ontology.instAlexandrovDiscreteItemSpace`).  And so on.
-/

namespace Wikidata
namespace TheoryCorpus

open Wikidata Generated

/-- The Wikidata articles naming the theories that this development attaches to
the pullback — the seeds of `data/theories.wdkb`, and the entities of the last
block of `Wikidata.vocabulary`. -/
def theoryArticles : List String :=
  ["Q42989",      -- topology
   "Q179899",     -- topological space
   "Q3532117",    -- Alexandrov topology
   "Q213363",     -- open set
   "Q170058",     -- continuous function
   "Q1062242",    -- Grothendieck topology
   "Q217413",     -- category theory
   "Q719395",     -- category
   "Q5891840",    -- homotopy type theory
   "Q110720714",  -- Identity type
   "Q493941",     -- fibration
   "Q139761564",  -- Cubical type theory
   "Q5244640",    -- De Morgan algebra
   "Q874429",     -- group theory
   "Q83478",      -- group
   "Q466109",     -- subgroup
   "Q60790315",   -- automorphism group
   "Q288465",     -- group action
   "Q903820",     -- field theory
   "Q190109",     -- field
   "Q5513324",    -- F₂
   "Q125977",     -- vector space
   "Q207643"]     -- linear map

/-- **The list is the seed list of the fragment**: each article is an item of the
downloaded knowledge base. -/
theorem theoryArticles_are_items :
    theoryArticles.all (fun q => Qid.wd q ∈ Theories.kb.items) = true := by native_decide

/-- **Each article names a construction of this library**: it occurs in the
vocabulary, which `Wikidata.Grounded.vocabulary_grounded` checks against the
downloaded glossary. -/
theorem theoryArticles_are_grounded :
    theoryArticles.all (fun q => vocabulary.any (fun t => t.entity == q)) = true := by
  native_decide

/-- Spelled out. -/
theorem exists_declaration_of_theoryArticle {q : String} (hq : q ∈ theoryArticles) :
    ∃ t ∈ vocabulary, t.entity = q := by
  have h2 := List.all_eq_true.1 theoryArticles_are_grounded q hq
  simp only [List.any_eq_true, beq_iff_eq] at h2
  obtain ⟨t, ht, hte⟩ := h2
  exact ⟨t, ht, hte⟩

/-! ### Agreements between Wikidata and the library -/

/-- Wikidata: **topology** (Q42989) is part of **mathematics** (Q395), and so is
**group theory** (Q874429). -/
theorem topology_subclass_mathematics :
    Theories.kb.isSubclassOf (Qid.wd "Q42989") (Qid.wd "Q395") = true := by native_decide

theorem groupTheory_subclass_mathematics :
    Theories.kb.isSubclassOf (Qid.wd "Q874429") (Qid.wd "Q395") = true := by native_decide

/-- Wikidata: an **Alexandrov topology** (Q3532117) is a **topology** (Q18786106).
Here: the `subclass of` hierarchy of an ontology carries the Alexandrov topology
`Ontology.subclassTopology`, and arbitrary intersections of open sets are open
(`Ontology.instAlexandrovDiscreteItemSpace`). -/
theorem alexandrov_subclass_topology :
    Theories.kb.isSubclassOf (Qid.wd "Q3532117") (Qid.wd "Q18786106") = true := by native_decide

/-- Wikidata: a **topological space** (Q179899) is a **mathematical structure**
(Q748349). Here: `Ontology.ItemSpace`. -/
theorem topologicalSpace_subclass_structure :
    Theories.kb.isSubclassOf (Qid.wd "Q179899") (Qid.wd "Q748349") = true := by native_decide

/-- Wikidata: a **Grothendieck topology** (Q1062242) is a **mathematical object**
(Q246672). Here: `Ontology.ontologyTopology`, the topology of jointly surjective
families, whose pullback-stability axiom is `Ontology.pbSnd_surjective_of_surjective`. -/
theorem grothendieck_subclass_object :
    Theories.kb.isSubclassOf (Qid.wd "Q1062242") (Qid.wd "Q246672") = true := by native_decide

/-- Wikidata: **homotopy type theory** (Q5891840) is a **type theory** (Q1056428)
and a **formal system** (Q649732). Here: the fibre product read as the type of
triples `(x, y, p)` with `p` a path (`Ontology.pullbackEquivSigma`). -/
theorem hott_subclass_typeTheory :
    Theories.kb.isSubclassOf (Qid.wd "Q5891840") (Qid.wd "Q1056428") = true := by native_decide

theorem hott_subclass_formalSystem :
    Theories.kb.isSubclassOf (Qid.wd "Q5891840") (Qid.wd "Q649732") = true := by native_decide

/-- Wikidata: a **fibration** (Q493941) is a **bundle** (Q1047307). Here: the
projection of the fibre product, whose fibre over an item is the fibre of the
other alignment (`Ontology.fibPbFstEquiv`). -/
theorem fibration_subclass_bundle :
    Theories.kb.isSubclassOf (Qid.wd "Q493941") (Qid.wd "Q1047307") = true := by native_decide

/-- Wikidata: a **De Morgan algebra** (Q5244640) is a **distributive lattice**
(Q2363730). Here: the cubical interval `Ontology.Iv`, with the De Morgan laws
`Ontology.Iv.deMorgan_meet` and `Ontology.Iv.deMorgan_join`. -/
theorem deMorgan_subclass_distributiveLattice :
    Theories.kb.isSubclassOf (Qid.wd "Q5244640") (Qid.wd "Q2363730") = true := by native_decide

/-- Wikidata: a **group** (Q83478) is a **monoid** (Q208237). Here: the
automorphisms of an ontology (`Ontology.autPerm`) are the invertible elements of
the monoid of its structure-preserving self-maps (`Ontology.endoSubmonoid`). -/
theorem group_subclass_monoid :
    Theories.kb.isSubclassOf (Qid.wd "Q83478") (Qid.wd "Q208237") = true := by native_decide

/-- Wikidata: a **subgroup** (Q466109) is a **group** (Q83478). Here: the
compatible triples of symmetries `Ontology.autOverSubgroup`, a `Subgroup` of the
product of the three automorphism groups. -/
theorem subgroup_subclass_group :
    Theories.kb.isSubclassOf (Qid.wd "Q466109") (Qid.wd "Q83478") = true := by native_decide

/-- Wikidata: an **automorphism group** (Q60790315) is a **group** (Q83478).
Here: `Ontology.autPerm`, the automorphisms of an ontology as permutations of its
items. -/
theorem automorphismGroup_subclass_group :
    Theories.kb.isSubclassOf (Qid.wd "Q60790315") (Qid.wd "Q83478") = true := by native_decide

/-- Wikidata: a **group action** (Q288465) is a **homomorphism** (Q215111). Here:
`Ontology.pbAut`, the homomorphism from compatible triples of symmetries to the
symmetries of the fibre product, and the action `Ontology.pbAutMulAction` it
induces on matched pairs. -/
theorem groupAction_subclass_homomorphism :
    Theories.kb.isSubclassOf (Qid.wd "Q288465") (Qid.wd "Q215111") = true := by native_decide

/-- Wikidata: a **field** (Q190109) is a **vector space** (Q125977), and a vector
space is a **free module** (Q1292333). Here: `GF(2)` and the extension space
`Ontology.ExtSpace`. -/
theorem field_subclass_vectorSpace :
    Theories.kb.isSubclassOf (Qid.wd "Q190109") (Qid.wd "Q125977") = true := by native_decide

theorem vectorSpace_subclass_freeModule :
    Theories.kb.isSubclassOf (Qid.wd "Q125977") (Qid.wd "Q1292333") = true := by native_decide

/-- Wikidata: a **linear map** (Q207643) is a **function** (Q11348). Here:
`Ontology.comapLin`, restriction of extensions along an alignment. -/
theorem linearMap_subclass_function :
    Theories.kb.isSubclassOf (Qid.wd "Q207643") (Qid.wd "Q11348") = true := by native_decide

/-- How many `subclass of` facts the fragment entails about these notions. -/
theorem theories_derivedSub_card : Theories.derivedSub.length = 923 := by native_decide

end TheoryCorpus
end Wikidata
