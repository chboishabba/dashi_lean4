import RequestProject.Vocabulary
import RequestProject.OntologyLimits
import RequestProject.OntologySheaves
import RequestProject.OntologyColimits
import RequestProject.Generated.Core
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

/-!
# The notions next door, and the download that covers them

`RequestProject.Vocabulary` matches every notion this development defines with
the Wikidata entity that names it.  Two things were missing, and this file
supplies both.

**The neighbours.**  `Wikidata.relatedNotions` continues the table with the
notions the later layers of the library turned out to need — the ones a reader of
`OntologyTopology`, `GrothendieckSite`, `OntologyLimits`, `OntologySheaves` and
`OntologyColimits` would look up: *Kolmogorov space*, *specialization
(pre)order*, *homeomorphism*, *forgetful functor*, *group homomorphism*,
*symmetric difference*, *presheaf*, *sheaf*, *monomorphism*, *epimorphism*,
*initial object*, *terminal object*, *natural transformation*, *coproduct*,
*colimit*, *faithful functor* and *concrete category*.  As in `Vocabulary`, each
entry is a name literal, so Lean itself rejects an entry naming a declaration
that does not exist.

**The download.**  A notion was *named* by the library but, in most cases, never
*queried*: of the 160 Wikidata items the two tables mention, 93 were not in any
downloaded fragment (`Notions.notions_needing_new_downloads_card`).  The new
fragments — the four rounds of the frontier, `data/vocabulary.wdkb`,
`data/related.wdkb`, `data/related2.wdkb` and `data/knowledge.wdkb` — close that
gap: every item named by either table is now declared by a downloaded fragment
(`Notions.notions_all_downloaded`, with
`Notions.notions_all_downloaded_mem` spelling out what that means).
-/

namespace Wikidata

/-- The notions of the later layers of the library, each with the Wikidata
entity that names it.  A continuation of `Wikidata.vocabulary`. -/
def relatedNotions : List GroundedTerm :=
  [ -- ## The item space of an ontology (`RequestProject.OntologyTopology`)
    ⟨``Wikidata.Ontology.instT0SpaceItemSpace, "Q1148924", "Kolmogorov space"⟩,
    ⟨``Wikidata.Ontology.specializes_iff_subclassOf, "Q5569420", "specialization (pre)order"⟩,
    ⟨``Wikidata.Ontology.isHomeomorph_pbCompare_of_componentwise, "Q202906", "homeomorphism"⟩,
    -- ## The category of ontologies (`CategoryOfOntologies`, `OntologyLimits`)
    ⟨``Wikidata.Ontology.forgetOnt, "Q2646117", "forgetful functor"⟩,
    ⟨``Wikidata.Ontology.mono_iff_injective, "Q1945067", "monomorphism"⟩,
    ⟨``Wikidata.Ontology.epi_of_surjective, "Q1347208", "epimorphism"⟩,
    ⟨``Wikidata.Ontology.isInitial_emptyOnt, "Q10535634", "initial object"⟩,
    ⟨``Wikidata.Ontology.no_isTerminal, "Q91432273", "terminal object"⟩,
    -- ## The site and its sheaves (`GrothendieckSite`, `OntologySheaves`)
    ⟨``Wikidata.Ontology.funPresheaf, "Q7241077", "presheaf"⟩,
    ⟨``Wikidata.Ontology.funSheaf, "Q595298", "sheaf"⟩,
    ⟨``Wikidata.Ontology.funPresheafMap, "Q1442189", "natural transformation"⟩,
    -- ## Colimits and concreteness (`OntologyColimits`)
    ⟨``Wikidata.Ontology.isColimit_sumCofan, "Q692689", "coproduct"⟩,
    ⟨``Wikidata.Ontology.instHasBinaryCoproductsOnt, "Q111204834", "colimit"⟩,
    ⟨``Wikidata.Ontology.forgetOnt_faithful, "Q12175350", "faithful functor"⟩,
    ⟨``Wikidata.Ontology.eq_of_forget_eq, "Q1575634", "concrete category"⟩,
    -- ## Symmetries and extensions (`OntologyGroups`, `OntologyFields`)
    ⟨``Wikidata.Ontology.pbAut, "Q868169", "group homomorphism"⟩,
    ⟨``Wikidata.Ontology.chi_symmDiff, "Q1147242", "symmetric difference"⟩ ]

namespace Notions

open Wikidata.Generated

/-- The fragments that had been downloaded before: the merged corpus, the
mathematical structures and the theories. -/
def priorFragments : List KB := [Core.kb, Structures.kb, Theories.kb]

/-- The eight fragments downloaded to close the gaps: four rounds of the frontier
of the crawl, the notions the vocabulary names, the structures related to them,
the categorical structures of the later layers, and the vocabulary of knowledge
representation itself. -/
def newFragments : List KB :=
  [Frontier.kb, Frontier2.kb, Frontier3.kb, Frontier4.kb, VocabularyCorpus.kb,
    RelatedStructures.kb, RelatedStructures2.kb, KnowledgeRepresentation.kb]

/-- Every notion of the library, with the Wikidata entity naming it. -/
def allNotions : List GroundedTerm := vocabulary ++ relatedNotions

/-- Is this entity an item (rather than a property) declared by one of the given
fragments? -/
def coveredBy (kbs : List KB) (t : GroundedTerm) : Bool :=
  !t.entity.startsWith "Q" || kbs.any (fun kb => kb.items.contains (Qid.wd t.entity))

/-- How many notions the two tables name: 191 entries, of which 160 are Wikidata
items and the rest Wikidata properties. -/
theorem allNotions_card : allNotions.length = 191 := by native_decide

/-- The item entries among them. -/
theorem allNotions_item_card :
    (allNotions.filter (fun t => t.entity.startsWith "Q")).length = 160 := by native_decide

/-- **93 of the notions the library names had never been downloaded.** -/
theorem notions_needing_new_downloads_card :
    (allNotions.filter (fun t => !coveredBy priorFragments t)).length = 93 := by native_decide

/-- **And now every one of them is covered**: each Wikidata item named by the
vocabulary or by the table of related notions is declared by a downloaded
fragment. -/
theorem notions_all_downloaded :
    allNotions.all (coveredBy (priorFragments ++ newFragments)) = true := by native_decide

/-- What that means, spelled out: for every item named by either table there is a
downloaded fragment declaring it. -/
theorem notions_all_downloaded_mem (t : GroundedTerm) (ht : t ∈ allNotions)
    (hq : t.entity.startsWith "Q" = true) :
    ∃ kb ∈ priorFragments ++ newFragments, Qid.wd t.entity ∈ kb.items := by
  have h := List.all_eq_true.1 notions_all_downloaded t ht
  simp only [coveredBy, hq, Bool.not_true, Bool.false_or, List.any_eq_true,
    List.contains_iff_mem] at h
  obtain ⟨kb, hkb, hmem⟩ := h
  exact ⟨kb, hkb, hmem⟩

end Notions
end Wikidata
