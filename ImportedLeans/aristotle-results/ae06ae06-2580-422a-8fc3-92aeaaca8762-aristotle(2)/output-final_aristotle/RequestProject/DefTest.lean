import RequestProject.Defects
import RequestProject.Normalize
import RequestProject.Generated.Core
import RequestProject.Generated.Structures
import RequestProject.Generated.Frontier
import RequestProject.Generated.Frontier2
import RequestProject.Generated.Frontier3
import RequestProject.Generated.Frontier4
import RequestProject.Generated.VocabularyCorpus
import RequestProject.Generated.RelatedStructures
import RequestProject.Generated.RelatedStructures2
import RequestProject.Generated.KnowledgeRepresentation
import RequestProject.Generated.Theories
import RequestProject.Generated.Enriched

namespace Wikidata
namespace DefTest
open Wikidata.Generated

def corpus : KB :=
  (((((((((((Core.kb.merge Structures.kb).merge Frontier.kb).merge Frontier2.kb).merge
    Frontier3.kb).merge Frontier4.kb).merge VocabularyCorpus.kb).merge
    RelatedStructures.kb).merge RelatedStructures2.kb).merge
    KnowledgeRepresentation.kb).merge Theories.kb).merge Enriched.kb).normalize

theorem corpus_size :
    corpus.items.length = 1578 ∧ corpus.sub.length = 2257 ∧ corpus.inst.length = 1169 := by
  native_decide

theorem table_size : corpus.closureTable.length = 1578 := by native_decide

end DefTest
end Wikidata
