/-!
SLR-produced observation -> reviewed Wikidata query -> existing JMD Lean proof.

This module reuses JMD's checked P279 chain theorem. It does not claim that
a spaCy proper noun, candidate label, or parser dependency supplies an external
QID, reviewed alignment, provenance, or statement truth. Those are explicit
inputs owned by the SLR/ITIR world-repair review path.

JMD original theorem credit: meta-introspector/RequestProject.Cli.Derive.
DASHI source-attached integration: chboishabba.
-/
import RequestProject.Slr.Producer
import RequestProject.Cli.Derive

namespace Wikidata
namespace Slr

/-- A source-related query selected by a distinct reviewed mapping.
    In particular, membership of a PROPN candidate does *not* manufacture
    either QID, and a checked P279 chain is not an ontology-edit permission. -/
structure ReviewedSubclassQuery where
  observation : ProducerOutput
  originatingCandidate : Candidate
  candidateBelongsToSource :
    originatingCandidate ∈ observation.candidates.toList
  reviewReference : String
  alignmentReference : String
  sourceRevisionReference : String
  kb : KB
  alignedSubject : Qid
  alignedSuperclass : Qid
  checkedChain : List Qid
  chainAccepted :
    kb.checkSubChain alignedSubject checkedChain alignedSuperclass = true

/-- The actual JMD kernel theorem applies to a reviewed, source-attached
    question without giving parser observations extra semantic authority. -/
theorem reviewedSubClassChainSound (q : ReviewedSubclassQuery) :
    Relation.ReflTransGen q.kb.Sub q.alignedSubject q.alignedSuperclass :=
  KB.checkSubChain_sound q.kb q.alignedSubject q.checkedChain
    q.alignedSuperclass q.chainAccepted

/-- A Wiki source can be attached to a proof without becoming a proof premise:
    the only derivational premise is JMD's checked KB path. -/
theorem checkedChainDoesNotNeedParserPromotion (q : ReviewedSubclassQuery) :
    Relation.ReflTransGen q.kb.Sub q.alignedSubject q.alignedSuperclass :=
  reviewedSubClassChainSound q

end Slr
end Wikidata
