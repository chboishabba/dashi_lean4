import RequestProject.Generated.Glossary
import RequestProject.Vocabulary
import RequestProject.Generated.Core
import RequestProject.Generated.UpperOntology
import RequestProject.Generated.DouglasAdams
import RequestProject.Generated.Geography
import RequestProject.Generated.LifeSciences
import RequestProject.Generated.Society
import RequestProject.Generated.Events
import RequestProject.Generated.Chemistry
import RequestProject.Generated.CreativeWorks
import RequestProject.Generated.Mathematics
import RequestProject.Generated.Science
import RequestProject.Generated.Technology
import RequestProject.Generated.Structures
import RequestProject.Generated.Theories
import RequestProject.Generated.Frontier
import RequestProject.Generated.Frontier2
import RequestProject.Generated.VocabularyCorpus
import RequestProject.Generated.RelatedStructures
import RequestProject.Generated.RelatedStructures2
import RequestProject.Generated.KnowledgeRepresentation
import RequestProject.Generated.Frontier3
import RequestProject.Generated.Frontier4
import RequestProject.RelatedNotions

/-!
# Everything is grounded in Wikidata

This file is the check that the development says nothing about Wikidata that
Wikidata does not confirm.  Two things are checked, both against
`Wikidata.Generated.glossary` — the table downloaded from the Wikidata API by
`scripts/fetch_glossary.py`.

**The identifiers.**  `glossary_wellFormed` says the table is in good shape:
every identifier is well shaped, every entity has a label, and no identifier is
listed twice — so `lookup_unique` gives each identifier exactly one meaning.
`corpus_covered` says every Wikidata item of every downloaded fragment is in the
table, and `handwritten_covered` says the same of the hand-built ontologies of
the library.  So no item of this development is unexplained.

**The notions.**  `vocabulary_checks` says every notion of the formalisation
listed in `RequestProject.Vocabulary` is grounded in an entity the table knows,
*under the label the table records for it*: `Wikidata.MKB.isPartOfB` really is
the entity Wikidata labels `part of`, `Wikidata.Rank.preferred` really is the
one it labels `preferred rank`, and so on.  Since the entries of the vocabulary
are name literals, Lean has already checked that each names a declaration that
exists.

Every check is a `native_decide` evaluation of the executable predicates of
`RequestProject.Grounding`, whose meaning is fixed by the theorems there
(`Glossary.wellFormed_iff`, `Glossary.groundsKB_iff`, `Glossary.checksTerm_iff`).
-/

namespace Wikidata
namespace Grounded

open Wikidata Generated

/-! ### The glossary itself -/

/-- The downloaded glossary is well formed: well-shaped identifiers, no missing
label, no identifier listed twice. -/
theorem glossary_wellFormed : glossary.wellFormed = true := by native_decide

/-- How many entities the development is grounded in. -/
theorem glossary_size : glossary.entries.length = 1610 := by native_decide

/-- How many of them Wikidata links to an English Wikipedia article. -/
theorem glossary_articleCount : glossary.articleCount = 926 := by native_decide

/-- Exactly one of the identifiers the development uses is a redirect: `Q7184903`,
which Wikidata now answers as `Q7048977`. -/
theorem glossary_redirectCount : glossary.redirectCount = 1 := by native_decide

/-- Each entry is an item or a property, and not both. -/
theorem glossary_kinds : ∀ e ∈ glossary.entries,
    (e.isItem = true ∧ e.isProperty = false) ∨ (e.isProperty = true ∧ e.isItem = false) := by
  native_decide

/-- Each identifier has exactly one meaning: the entry the glossary finds for an
identifier is the only entry carrying it. -/
theorem lookup_unique {e : Gloss} (he : e ∈ glossary.entries) : glossary.lookup e.id = some e :=
  Glossary.lookup_eq_some_of_mem _ glossary_wellFormed he

/-! ### The downloaded corpus -/

/-- The twenty-two fragments downloaded from the Wikidata API — the fourteen the
development started from, and the eight that close its gaps: four rounds of the
frontier of the crawl, the notions the vocabulary names, the structures related
to them, the categorical structures of the later layers, and the vocabulary of
knowledge representation itself. -/
def corpus : List KB :=
  [Generated.Core.kb, Generated.UpperOntology.kb, Generated.DouglasAdams.kb,
    Generated.Geography.kb, Generated.LifeSciences.kb, Generated.Society.kb,
    Generated.Events.kb, Generated.Chemistry.kb, Generated.CreativeWorks.kb,
    Generated.Mathematics.kb, Generated.Science.kb, Generated.Technology.kb,
    Generated.Structures.kb, Generated.Theories.kb,
    Generated.Frontier.kb, Generated.Frontier2.kb, Generated.Frontier3.kb,
    Generated.Frontier4.kb, Generated.VocabularyCorpus.kb,
    Generated.RelatedStructures.kb, Generated.RelatedStructures2.kb,
    Generated.KnowledgeRepresentation.kb]

/-- Every item of every downloaded fragment is grounded. -/
theorem corpus_grounded : corpus.all glossary.groundsKB = true := by native_decide

/-- What that means: every Wikidata item named by the corpus has a glossary entry. -/
theorem corpus_covered (kb : KB) (hkb : kb ∈ corpus) (s : String) (hs : Qid.wd s ∈ kb.items) :
    glossary.grounds s = true :=
  (Glossary.groundsKB_iff _ kb).1 (List.all_eq_true.1 corpus_grounded kb hkb) s hs

/-! ### The hand-built ontologies of the library -/

/-- The ontologies written by hand in the library out of real Wikidata items. -/
def handwritten : List KB :=
  [Upper.wdBase, Taxonomy.taxonBase, Examples.wdCore, Examples.filmKB,
    StratumExample.tower, SubsumptionExample.frag, DisjointUnionExample.animalKB,
    AlignmentExample.wdFragment]

/-- Their items, too, are all grounded. -/
theorem handwritten_grounded : handwritten.all glossary.groundsKB = true := by native_decide

/-- What that means: every Wikidata item of a hand-built ontology has a glossary
entry as well. -/
theorem handwritten_covered (kb : KB) (hkb : kb ∈ handwritten) (s : String)
    (hs : Qid.wd s ∈ kb.items) : glossary.grounds s = true :=
  (Glossary.groundsKB_iff _ kb).1 (List.all_eq_true.1 handwritten_grounded kb hkb) s hs

/-! ### The vocabulary of the formalisation -/

/-- Every notion the formalisation defines is grounded in a Wikidata entity, and
that entity carries the label the vocabulary claims for it. -/
theorem vocabulary_checks : glossary.checksAll vocabulary = true := by native_decide

/-- What that means, spelled out. -/
theorem vocabulary_grounded (t : GroundedTerm) (ht : t ∈ vocabulary) :
    ∃ e, glossary.lookup t.entity = some e ∧ e.label = t.label :=
  (Glossary.checksTerm_iff _ t).1 ((Glossary.checksAll_iff _ vocabulary).1 vocabulary_checks t ht)

/-- No declaration of the library is grounded twice. -/
theorem vocabulary_decls_nodup : (vocabulary.map GroundedTerm.decl).Nodup := by native_decide

/-- How many notions of the formalisation are grounded. -/
theorem vocabulary_size : vocabulary.length = 174 := by native_decide

/-! ### The notions of the later layers -/

/-- Every notion of `Wikidata.relatedNotions` — the neighbours the later layers
of the library needed — is grounded in a Wikidata entity carrying the label the
table claims for it. -/
theorem relatedNotions_checks : glossary.checksAll relatedNotions = true := by native_decide

/-- What that means, spelled out. -/
theorem relatedNotions_grounded (t : GroundedTerm) (ht : t ∈ relatedNotions) :
    ∃ e, glossary.lookup t.entity = some e ∧ e.label = t.label :=
  (Glossary.checksTerm_iff _ t).1
    ((Glossary.checksAll_iff _ relatedNotions).1 relatedNotions_checks t ht)

/-- No declaration is grounded twice in the new table. -/
theorem relatedNotions_decls_nodup : (relatedNotions.map GroundedTerm.decl).Nodup := by
  native_decide

/-- And no Wikidata entity is claimed twice across the two tables. -/
theorem allNotions_entities_nodup : (Notions.allNotions.map GroundedTerm.entity).Nodup := by
  native_decide

/-! ### Looking things up -/

/-- info: some "subclass of" -/
#guard_msgs in
#eval (glossary.lookup "P279").map Gloss.label

/-- info: some "https://www.wikidata.org/wiki/Property:P279" -/
#guard_msgs in
#eval (glossary.lookup "P279").map Gloss.conceptUrl

/-- info: some (some "https://en.wikipedia.org/wiki/Douglas_Adams") -/
#guard_msgs in
#eval (glossary.lookup "Q42").map Gloss.articleUrl

#eval (glossary.lookup "Q16521").map Gloss.render

end Grounded
end Wikidata
