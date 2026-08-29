import RequestProject.Generated.RelatedStructures
import RequestProject.Generated.RelatedStructures2
import RequestProject.Generated.KnowledgeRepresentation
import RequestProject.Normalize
import RequestProject.Merge

/-!
# Two more neighbourhoods of the ontology

The downloads so far followed the crawl: the seeds of `data/core.wdkb`, then the
items those mention.  This file adds two neighbourhoods that no crawl was going
to reach, because they are neighbours of the *formalisation* rather than of the
seeds.

**The categorical structures** (`data/related2.wdkb`, compiled to
`RequestProject.Generated.RelatedStructures2`).  `RequestProject.OntologyLimits`
and `RequestProject.OntologySheaves` work with limits, colimits, sheaves and the
categories they live in; `data/related.wdkb` had covered the first batch of those
notions and this fragment adds the rest — *equaliser*, *coequalizer*, *pushout*,
*coproduct*, *colimit*, *comma category*, *functor category*, *monoidal
category*, *cartesian closed category*, *topos*, *subobject classifier* and
*concrete category*.  `Corpus.categorical` merges the two fragments, and the
theorems below read the resulting hierarchy: a topos is a cartesian closed
category, hence a monoidal category, hence a mathematical structure; equalisers
are limits, coequalizers and pushouts are colimits, and Wikidata records both as
Kan extensions.

**The knowledge-representation vocabulary** (`data/knowledge.wdkb`, compiled to
`RequestProject.Generated.KnowledgeRepresentation`).  Wikidata is one member of a
family — *OWL*, *RDF Schema*, *SKOS*, *SPARQL*, *description logic*, *ontology
language*, *semantic reasoner*, *semantic network*, *controlled vocabulary*,
*thesaurus*, *class hierarchy*, *meronymy* — and none of it was in the corpus.
`Corpus.knowledge` is that download, and the theorems record how Wikidata
classifies its own subject matter: OWL is an ontology language, SKOS is an
ontology, SPARQL is a programming language, a thesaurus is a controlled
vocabulary, a semantic network is a knowledge graph, and a semantic reasoner is
software.

Every fact below is stated on the *derived* relations — `Relation.ReflTransGen`
of the asserted `subclass of` statements, and the instance relation closed under
it — and obtained from the certified queries of `RequestProject.Engine`, so each
one is a genuine consequence of the downloaded statements.
-/

namespace Wikidata
namespace Corpus

open Wikidata.Generated

/-! ## The categorical structures -/

/-- The two fragments of categorical notions, merged and deduplicated. -/
def categorical : KB := (RelatedStructures.kb.merge RelatedStructures2.kb).normalize

/-- It is well formed, so the certified queries apply to it. -/
theorem categorical_wellFormed : categorical.wellFormed = true :=
  KB.normalize_wellFormed
    (KB.wellFormed_merge RelatedStructures.kb_wellFormed RelatedStructures2.kb_wellFormed)

/-- It entails the first fragment … -/
theorem categorical_entails_related : categorical.Entails RelatedStructures.kb = true :=
  KB.entails_trans categorical_wellFormed
    (KB.wellFormed_merge RelatedStructures.kb_wellFormed RelatedStructures2.kb_wellFormed)
    (KB.normalize_entails
      (KB.wellFormed_merge RelatedStructures.kb_wellFormed RelatedStructures2.kb_wellFormed))
    (KB.merge_entails_left RelatedStructures.kb_wellFormed RelatedStructures2.kb_wellFormed)

/-- … and the second. -/
theorem categorical_entails_related2 : categorical.Entails RelatedStructures2.kb = true :=
  KB.entails_trans categorical_wellFormed
    (KB.wellFormed_merge RelatedStructures.kb_wellFormed RelatedStructures2.kb_wellFormed)
    (KB.normalize_entails
      (KB.wellFormed_merge RelatedStructures.kb_wellFormed RelatedStructures2.kb_wellFormed))
    (KB.merge_entails_right RelatedStructures.kb_wellFormed RelatedStructures2.kb_wellFormed)

/-- How many items the merged fragment knows about. -/
theorem categorical_card : categorical.items.length = 181 := by native_decide

/-- **A topos is a cartesian closed category** (`Q2143621` ⊑ `Q1725874`). -/
theorem topos_sub_cartesianClosed :
    Relation.ReflTransGen categorical.Sub (Qid.wd "Q2143621") (Qid.wd "Q1725874") :=
  (KB.isSubclassOf_iff categorical_wellFormed _ _).1 (by native_decide)

/-- … and therefore a monoidal category (`Q1945014`). -/
theorem topos_sub_monoidal :
    Relation.ReflTransGen categorical.Sub (Qid.wd "Q2143621") (Qid.wd "Q1945014") :=
  (KB.isSubclassOf_iff categorical_wellFormed _ _).1 (by native_decide)

/-- … and a mathematical structure (`Q748349`), and so an entity (`Q35120`). -/
theorem topos_sub_mathematicalStructure :
    Relation.ReflTransGen categorical.Sub (Qid.wd "Q2143621") (Qid.wd "Q748349") :=
  (KB.isSubclassOf_iff categorical_wellFormed _ _).1 (by native_decide)

theorem topos_sub_entity :
    Relation.ReflTransGen categorical.Sub (Qid.wd "Q2143621") (Qid.wd "Q35120") :=
  (KB.isSubclassOf_iff categorical_wellFormed _ _).1 (by native_decide)

/-- **An equaliser is a limit** (`Q1224487` ⊑ `Q1322614`). -/
theorem equaliser_sub_limit :
    Relation.ReflTransGen categorical.Sub (Qid.wd "Q1224487") (Qid.wd "Q1322614") :=
  (KB.isSubclassOf_iff categorical_wellFormed _ _).1 (by native_decide)

/-- **A coequalizer is a colimit** (`Q5140810` ⊑ `Q111204834`). -/
theorem coequalizer_sub_colimit :
    Relation.ReflTransGen categorical.Sub (Qid.wd "Q5140810") (Qid.wd "Q111204834") :=
  (KB.isSubclassOf_iff categorical_wellFormed _ _).1 (by native_decide)

/-- **A pushout is a colimit** (`Q1633079` ⊑ `Q111204834`) — the colimit that
`RequestProject.CategoryOfOntologies` dualises when it builds fibre products. -/
theorem pushout_sub_colimit :
    Relation.ReflTransGen categorical.Sub (Qid.wd "Q1633079") (Qid.wd "Q111204834") :=
  (KB.isSubclassOf_iff categorical_wellFormed _ _).1 (by native_decide)

/-- Wikidata also records limits and colimits as Kan extensions (`Q1723418`),
so a pushout is one. -/
theorem pushout_sub_kanExtension :
    Relation.ReflTransGen categorical.Sub (Qid.wd "Q1633079") (Qid.wd "Q1723418") :=
  (KB.isSubclassOf_iff categorical_wellFormed _ _).1 (by native_decide)

/-- **A sheaf is a presheaf** (`Q595298` ⊑ `Q7241077`): the fact that
`Wikidata.Ontology.funSheaf` instantiates, since it is built from
`Wikidata.Ontology.funPresheaf`. -/
theorem sheaf_sub_presheaf :
    Relation.ReflTransGen categorical.Sub (Qid.wd "Q595298") (Qid.wd "Q7241077") :=
  (KB.isSubclassOf_iff categorical_wellFormed _ _).1 (by native_decide)

/-! ## The knowledge-representation vocabulary -/

/-- The download about knowledge representation itself, deduplicated. -/
def knowledge : KB := KnowledgeRepresentation.kb.normalize

/-- It is well formed. -/
theorem knowledge_wellFormed : knowledge.wellFormed = true :=
  KB.normalize_wellFormed KnowledgeRepresentation.kb_wellFormed

/-- It entails the download it came from. -/
theorem knowledge_entails_download : knowledge.Entails KnowledgeRepresentation.kb = true :=
  KB.normalize_entails KnowledgeRepresentation.kb_wellFormed

/-- How many items it knows about. -/
theorem knowledge_card : knowledge.items.length = 150 := by native_decide

/-- **OWL is an ontology language** (`Q826165` : `Q7095059`). -/
theorem owl_inst_ontologyLanguage :
    ∃ d, knowledge.Inst (Qid.wd "Q826165") d ∧
      Relation.ReflTransGen knowledge.Sub d (Qid.wd "Q7095059") :=
  (KB.isInstanceOf_iff knowledge_wellFormed _ _).1 (by native_decide)

/-- **SKOS is an ontology** (`Q2288360` : `Q324254`). -/
theorem skos_inst_ontology :
    ∃ d, knowledge.Inst (Qid.wd "Q2288360") d ∧
      Relation.ReflTransGen knowledge.Sub d (Qid.wd "Q324254") :=
  (KB.isInstanceOf_iff knowledge_wellFormed _ _).1 (by native_decide)

/-- **SPARQL is a programming language** (`Q54871` : `Q9143`). -/
theorem sparql_inst_programmingLanguage :
    ∃ d, knowledge.Inst (Qid.wd "Q54871") d ∧
      Relation.ReflTransGen knowledge.Sub d (Qid.wd "Q9143") :=
  (KB.isInstanceOf_iff knowledge_wellFormed _ _).1 (by native_decide)

/-- **RDF Schema is a controlled vocabulary** (`Q1751819` : `Q1469824`). -/
theorem rdfs_inst_controlledVocabulary :
    ∃ d, knowledge.Inst (Qid.wd "Q1751819") d ∧
      Relation.ReflTransGen knowledge.Sub d (Qid.wd "Q1469824") :=
  (KB.isInstanceOf_iff knowledge_wellFormed _ _).1 (by native_decide)

/-- **A thesaurus is a controlled vocabulary** (`Q17152639` ⊑ `Q1469824`). -/
theorem thesaurus_sub_controlledVocabulary :
    Relation.ReflTransGen knowledge.Sub (Qid.wd "Q17152639") (Qid.wd "Q1469824") :=
  (KB.isSubclassOf_iff knowledge_wellFormed _ _).1 (by native_decide)

/-- **A semantic network is a knowledge graph** (`Q1045785` ⊑ `Q33002955`). -/
theorem semanticNetwork_sub_knowledgeGraph :
    Relation.ReflTransGen knowledge.Sub (Qid.wd "Q1045785") (Qid.wd "Q33002955") :=
  (KB.isSubclassOf_iff knowledge_wellFormed _ _).1 (by native_decide)

/-- **A semantic reasoner is software** (`Q3929429` ⊑ `Q7397`) — the kind of
program `RequestProject.Engine` is a verified instance of. -/
theorem semanticReasoner_sub_software :
    Relation.ReflTransGen knowledge.Sub (Qid.wd "Q3929429") (Qid.wd "Q7397") :=
  (KB.isSubclassOf_iff knowledge_wellFormed _ _).1 (by native_decide)

end Corpus
end Wikidata
