import RequestProject.Slr.GwbP4ArticleEndToEnd
import RequestProject.Slr.DbSourceProducer
import RequestProject.Slr.GwbWorldGraphProof
import RequestProject.Slr.FiniteConsumerCertificate

/-!
GWB P5–P10 single-object maximum-cut ledger.

This reuses the actual original GWB typed Rust receipt, original SLR
DB-M12/S28 checks and JMD EntityData property semantics. It introduces
NO NLP producer, simulated review, event ontology, or inferred truth.

Unlike source-only P4, the semantic gates require actual reviewed
witnesses. The original committed SLR receipt marks all those
authorities unpaid, so the unconditional article-specific theorem is
intentionally NOT available.

P5 review: original mention/referent identity relation
P6 event: M12 source literal and S28 ancestry, plus explicit identity
P7 time: event-scoped temporal evidence and temporal interpretation
P8 coverage: all production-live readings, not candidate enumeration
P9 alignment: explicit reviewed article/JMD proposition equivalence
P10 expansion: each supported independently imported JMD statement
-/

namespace Wikidata
namespace Slr
namespace GwbP5P10

open Lean
open GwbTypedFibre

/-- The semantic question remains tied to its original, checked article
    and Rust typed source. This is not yet an identity resolution. -/
structure SourceAnchor
    {article : String} {slr projection native : Json} where
  checked : CheckedRows article slr projection native
  sentenceIndex : Nat
  sentencePresent : checked.rows.toList.any
    (fun row => row.sentenceIndex == sentenceIndex) = true
  mentionRef : String
  nonemptyMention : mentionRef ≠ ""

/-- P5 review must be *about the same source anchor* and carry a
    proof-relevant mapping; a generic "reviewed=true" is insufficient.
    No producer-generated identity is accepted merely by association. -/
structure ReviewedIdentity
    {article : String} {slr projection native : Json}
    (anchor : SourceAnchor (article := article) (slr := slr)
      (projection := projection) (native := native)) where
  referent : String
  nonemptyReferent : referent ≠ ""
  reviewedSourceMention : Prop
  reviewedEvidence : reviewedSourceMention
  identityRelation : Prop
  acceptedRelation : identityRelation

/-- Review does not rewrite the candidate set or original source identity. -/
theorem p5OriginalSourceSurvivesReview
    {article : String} {slr projection native : Json}
    {anchor : SourceAnchor (article := article) (slr := slr)
      (projection := projection) (native := native)}
    (review : ReviewedIdentity anchor) :
    GwbNativeFibre.checkRealGwbNativeFibreReceipt
      article slr projection native = true :=
  GwbTypedFibre.typedRowsRemainSourceBound anchor.checked

/-- P6 must consume independently checked original SLR DB products.
    The event semantic-equivalence relation is a *separate* reviewed
    proof, not the same thing as S28 source ancestry. -/
structure ReviewedEvent
    {article : String} {slr projection native : Json}
    {anchor : SourceAnchor (article := article) (slr := slr)
      (projection := projection) (native := native)}
    (identity : ReviewedIdentity anchor)
    (literal : String) (m12 : DbM12Observation)
    (s28 : Json) (eventRef : String) where
  originalM12 : CheckedNativeM12Literal literal m12
  originalS28 : CheckedS28Provenance s28 eventRef
  statementRefMatches : Prop
  statementMatched : statementRefMatches
  originalMentionEventRelation : Prop
  eventRelationReviewed : originalMentionEventRelation
  identityEventRelation : Prop
  identityRelationReviewed : identityEventRelation

/-- The DB M12 literal and S28 ancestry are retained as independent
    certificates, without converting adjacency into historical truth. -/
theorem p6PreservesBothOriginalChecks
    {article : String} {slr projection native : Json}
    {anchor : SourceAnchor (article := article) (slr := slr)
      (projection := projection) (native := native)}
    {identity : ReviewedIdentity anchor}
    {literal : String} {m12 : DbM12Observation}
    {s28 : Json} {eventRef : String}
    (event : ReviewedEvent identity literal m12 s28 eventRef) :
    checkNativeM12Literal literal m12 = true ∧
    checkS28Provenance s28 eventRef = true :=
  ⟨checkedM12AllSourceSpansExact event.originalM12,
    checkedS28HasCompleteAncestry event.originalS28⟩

/-- P7 temporal truth is not sourced from the candidate-only S28 row.
    It requires a reviewed event-time relation bound to the same event. -/
structure ReviewedTemporal
    {article : String} {slr projection native : Json}
    {anchor : SourceAnchor (article := article) (slr := slr)
      (projection := projection) (native := native)}
    {identity : ReviewedIdentity anchor}
    {literal : String} {m12 : DbM12Observation}
    {s28 : Json} {eventRef : String}
    (event : ReviewedEvent identity literal m12 s28 eventRef) where
  timeRef : String
  nonemptyTimeRef : timeRef ≠ ""
  temporalSourceRelation : Prop
  temporalSourceReviewed : temporalSourceRelation
  temporalEventMeaning : Prop
  temporalMeaningReviewed : temporalEventMeaning

/-- P8: semantic consumer closure requires the EXISTING original
    proof-relevant SourceQueryLicence. A finite compiler list cannot
    substitute for complete production-live readings. -/
structure ReviewedConsumer
    {Source Observation Reading Query Answer : Type}
    (model : DocumentQueryModel Source Observation Reading Query Answer)
    (source : Source) (query : Query) where
  licence : SourceQueryLicence model source query

theorem p8ConsumerAnswerSound
    {Source Observation Reading Query Answer : Type}
    {model : DocumentQueryModel Source Observation Reading Query Answer}
    {source : Source} {query : Query}
    (consumer : ReviewedConsumer model source query) (answer : Answer)
    (evaluated :
      model.readingAnswer consumer.licence.chosenReading query = answer) :
    model.documentAnswer source query = answer :=
  slrJmdDocumentQuerySound consumer.licence answer evaluated

/-- P9 is not satisfied by mere Q207 title/sitelink correspondence:
    semantic alignment of a specific article proposition with a
    specific independently checked JMD property must itself be reviewed. -/
structure ReviewedArticleKBAlignment
    {article : String} {slr projection native wikidata : Json}
    (root : GwbArticleIdentity.CheckedGwbRootIdentity
      article slr projection wikidata)
    (source : CheckedRows article slr projection native)
    (property : GwbWorldGraph.CheckedWorldProperty) where
  sourcePropositionAlignment : Prop
  articlePropertyReviewed : sourcePropositionAlignment
  sameArticleSubject : property.subject = Qid.wd "Q207"

/-- P10: proof-preserving graph expansion is relative to the JMD
    independently imported property checker, NOT SLR's graph candidate
    alone; all edges must be individually supported for total coverage. -/
structure CompletelyCheckedWorld
    (graph : Json) (kb : PKB) where
  candidateSource : GwbWorldGraph.CheckedCandidateWorldGraph graph
  everyEdgeSupported :
    ∀ edge ∈ (graph.getObjValAs? (Array Json)
      "item_property_edges").toOption.getD #[],
      ∃ proof : GwbWorldGraph.CheckedWorldProperty,
        GwbWorldGraph.proofForEdge? kb edge = some proof

/-- Every graph edge then has a JMD-native KB witness. This proves KB
    support, not historical world truth or multi-QID snapshot simultaneity. -/
theorem p10AllEdgesJmdSupported
    {graph : Json} {kb : PKB}
    (world : CompletelyCheckedWorld graph kb) :
    ∀ edge ∈ (graph.getObjValAs? (Array Json)
      "item_property_edges").toOption.getD #[],
      ∃ proof : GwbWorldGraph.CheckedWorldProperty,
        GwbWorldGraph.proofForEdge? kb edge = some proof :=
  world.everyEdgeSupported

/-- Composition of stages P5–P10 for the exact source object.
    All distinct empirical/review obligations are explicit arguments.
    No event truth or actor identity may be derived from the source-only
    P4 certificate, M12/S28 candidate flags or a JMD QID match. -/
theorem fullChainKeepsSeparateEvidence
    {article : String} {slr projection native wikidata : Json}
    (root : GwbArticleIdentity.CheckedGwbRootIdentity
      article slr projection wikidata)
    {anchor : SourceAnchor (article := article) (slr := slr)
      (projection := projection) (native := native)}
    (identity : ReviewedIdentity anchor)
    {literal : String} {m12 : DbM12Observation}
    {s28 : Json} {eventRef : String}
    (event : ReviewedEvent identity literal m12 s28 eventRef)
    (temporal : ReviewedTemporal event)
    (property : GwbWorldGraph.CheckedWorldProperty)
    (alignment : ReviewedArticleKBAlignment root anchor.checked property)
    {graph : Json} {kb : PKB}
    (world : CompletelyCheckedWorld graph kb) :
    GwbArticleIdentity.checkGwbRootIdentity
      article slr projection wikidata = true ∧
    GwbNativeFibre.checkRealGwbNativeFibreReceipt
      article slr projection native = true ∧
    checkNativeM12Literal literal m12 = true ∧
    checkS28Provenance s28 eventRef = true ∧
    property.subject = Qid.wd "Q207" ∧
    (∀ edge ∈ (graph.getObjValAs? (Array Json)
        "item_property_edges").toOption.getD #[],
      ∃ proof : GwbWorldGraph.CheckedWorldProperty,
        GwbWorldGraph.proofForEdge? kb edge = some proof) := by
  exact ⟨GwbArticleIdentity.checkedGwbRootSourceAndSitelink root,
    p5OriginalSourceSurvivesReview identity,
    (p6PreservesBothOriginalChecks event).1,
    (p6PreservesBothOriginalChecks event).2,
    alignment.sameArticleSubject,
    p10AllEdgesJmdSupported world⟩

/-- P9 alone supplies article-source and JMD KB property *separately*,
    never silently converting textual claims into imported statements. -/
theorem p9AlignmentRetainsIndependentChecks
    {article : String} {slr projection native wikidata : Json}
    {root : GwbArticleIdentity.CheckedGwbRootIdentity
      article slr projection wikidata}
    {source : CheckedRows article slr projection native}
    {property : GwbWorldGraph.CheckedWorldProperty}
    (alignment : ReviewedArticleKBAlignment root source property) :
    GwbArticleIdentity.checkGwbRootIdentity
      article slr projection wikidata = true ∧
    GwbNativeFibre.checkRealGwbNativeFibreReceipt
      article slr projection native = true ∧
    (∃ p, (p, property.subject, property.object) ∈
      property.pkb.stmts ∧
      property.pkb.isSubPropertyOf p property.property = true) :=
  ⟨GwbArticleIdentity.checkedGwbRootSourceAndSitelink root,
    GwbTypedFibre.typedRowsRemainSourceBound source,
    GwbWorldGraph.checkedWorldPropertySound property⟩

end GwbP5P10
end Slr
end Wikidata
