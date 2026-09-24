import RequestProject.Generated.Structures
import RequestProject.MathResonance
import RequestProject.Vocabulary

/-!
# The mathematics articles of Wikidata, and what they say about this library

`RequestProject.MathResonance` restates the constructions of this development in
Mathlib's vocabulary, and `RequestProject.Vocabulary` records which **Wikidata
article** names each of them.  This file closes the loop with the data: the
fragment `RequestProject.Generated.Structures` was downloaded from Wikidata with
exactly those articles as its seeds, so what Wikidata says *about the notions the
library is made of* is itself an ontology this library can check.

Three things are proved here.

* `mathArticles_are_items` — every article of the resonance list really is an
  item of the downloaded fragment;
* `mathArticles_are_grounded` — every one of them is matched, in
  `Wikidata.vocabulary`, with a declaration of this library;
* a handful of *agreements*: a `subclass of` fact that Wikidata asserts about
  those notions, next to the theorem of this library that says the same thing
  about the constructions grounded in them.  Wikidata says a bijection is an
  injection and a surjection; here, the meta lift is injective
  (`KB.metaLift_injective`), surjective onto the meta-written bases
  (`KB.metaLift_surjective_onto_allMeta`) and a bijection
  (`KB.metaEquiv_bijective`).  Wikidata says a pullback is a limit; here, the
  fibre product of two ontologies has the universal property of a limit
  (`Ontology.pullback.lift`, `Ontology.pullback.lift_unique`).  And so on.
-/

namespace Wikidata
namespace MathCorpus

open Wikidata Generated

/-- The Wikidata articles that name the mathematical notions this development is
made of — the seeds of `data/structures.wdkb`, and the entities of the last block
of `Wikidata.vocabulary`. -/
def mathArticles : List String :=
  ["Q215111",    -- homomorphism
   "Q208237",    -- monoid
   "Q11077412",  -- strict order
   "Q1425985",   -- preorder
   "Q1397439",   -- pullback
   "Q1322614",   -- limit
   "Q1417809",   -- universal property
   "Q621542",    -- commutative diagram
   "Q2141963",   -- retract
   "Q44106280",  -- idempotent function
   "Q217608",    -- fixed point
   "Q864213",    -- Conservative extension
   "Q357858",    -- adjoint functor
   "Q48998319",  -- Frobenius reciprocity
   "Q381060",    -- partition of a set
   "Q182003",    -- injection
   "Q229102",    -- surjective function
   "Q180907",    -- bijection
   "Q189112",    -- isomorphism
   "Q368988",    -- idempotence
   "Q130998",    -- equivalence relation
   "Q3966112",   -- quotient set
   "Q338021",    -- well-founded relation
   "Q430001",    -- decidability
   "Q693083",    -- soundness
   "Q15846555",  -- completeness
   "Q6134913",   -- Least fixed point
   "Q42866132",  -- upper bound
   "Q54980267",  -- intransitivity
   "Q1609475",   -- Herbrand structure
   "Q1308999",   -- restriction
   "Q1137726"]   -- directed graph

/-- **The list is the seed list of the fragment**: each article is an item of the
downloaded knowledge base. -/
theorem mathArticles_are_items :
    mathArticles.all (fun q => Qid.wd q ∈ Structures.kb.items) = true := by native_decide

/-- **Each article names a construction of this library**: it occurs in the
vocabulary, which `Wikidata.Grounded.vocabulary_grounded` checks against the
downloaded glossary. -/
theorem mathArticles_are_grounded :
    mathArticles.all (fun q => vocabulary.any (fun t => t.entity == q)) = true := by
  native_decide

/-- Spelled out. -/
theorem exists_declaration_of_mathArticle {q : String} (hq : q ∈ mathArticles) :
    ∃ t ∈ vocabulary, t.entity = q := by
  have h2 := List.all_eq_true.1 mathArticles_are_grounded q hq
  simp only [List.any_eq_true, beq_iff_eq] at h2
  obtain ⟨t, ht, hte⟩ := h2
  exact ⟨t, ht, hte⟩

/-! ### Agreements between Wikidata and the library

Each pair below is a fact Wikidata asserts about these notions, and the theorem
of this development that says the same about the constructions grounded in them.
-/

/-- Wikidata: a **bijection** (Q180907) is an **injection** (Q182003). Here:
`KB.metaLift_injective`. -/
theorem bijection_subclass_injection :
    Structures.kb.isSubclassOf (Qid.wd "Q180907") (Qid.wd "Q182003") = true := by native_decide

/-- Wikidata: a **bijection** (Q180907) is a **surjective function** (Q229102).
Here: `KB.metaLift_surjective_onto_allMeta`. -/
theorem bijection_subclass_surjection :
    Structures.kb.isSubclassOf (Qid.wd "Q180907") (Qid.wd "Q229102") = true := by native_decide

/-- Wikidata: a **pullback** (Q1397439) is a **limit** (Q1322614). Here:
`Ontology.pullback.lift` and `Ontology.pullback.lift_unique` are the existence and
uniqueness halves of the universal property that makes the fibre product a
limit. -/
theorem pullback_subclass_limit :
    Structures.kb.isSubclassOf (Qid.wd "Q1397439") (Qid.wd "Q1322614") = true := by native_decide

/-- Wikidata: an **equivalence relation** (Q130998) is a **preorder** (Q1425985).
Here: `KB.renameSetoid` is an equivalence relation and `WellFormedKB.instPreorder`
a preorder — and the latter is *not* an equivalence relation nor a partial order
(`WellFormedKB.not_antisymm`). -/
theorem equivalence_subclass_preorder :
    Structures.kb.isSubclassOf (Qid.wd "Q130998") (Qid.wd "Q1425985") = true := by native_decide

/-- Wikidata: a **preorder** (Q1425985) is a **transitive relation** (Q64861) —
the entity already grounded in `Ontology.subclassOf_trans`. -/
theorem preorder_subclass_transitive :
    Structures.kb.isSubclassOf (Qid.wd "Q1425985") (Qid.wd "Q64861") = true := by native_decide

/-- Wikidata: a **strict order** (Q11077412) is a **transitive relation**
(Q64861). Here: `Ontology.properSubclassOf_isStrictOrder`. -/
theorem strictOrder_subclass_transitive :
    Structures.kb.isSubclassOf (Qid.wd "Q11077412") (Qid.wd "Q64861") = true := by native_decide

/-- Wikidata: an **adjoint functor** (Q357858) is a **functor** (Q864475). Here:
`Ontology.Alignment.pushPull_gc` — pushforward and pullback of class extensions
are monotone (`Alignment.push_mono`, `Alignment.pull_mono`) and adjoint. -/
theorem adjointFunctor_subclass_functor :
    Structures.kb.isSubclassOf (Qid.wd "Q357858") (Qid.wd "Q864475") = true := by native_decide

/-- Wikidata: an **idempotent function** (Q44106280) is an **idempotent element**
(Q2243424). Here: `KB.metaCore_isIdempotentElem` and
`Ontology.Retract.idem_isIdempotentElem` say exactly that, in the monoid
`Function.End`. -/
theorem idempotentFunction_subclass_idempotentElement :
    Structures.kb.isSubclassOf (Qid.wd "Q44106280") (Qid.wd "Q2243424") = true := by native_decide

/-- How many `subclass of` facts the fragment entails about these notions. -/
theorem structures_derivedSub_card : Structures.derivedSub.length = 502 := by native_decide

end MathCorpus
end Wikidata
