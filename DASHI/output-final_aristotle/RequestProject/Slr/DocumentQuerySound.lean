/-!
# Generic source-relative document-query soundness

The semantics are indexed by arbitrary source, interpretation, query and
answer types. This is the Lean consumer-side expression of the existing Agda
DASHI/Core/ConsumerDescentMinimalObserverExact and
DASHI/Reasoning/SemanticConsumerRelativeClosureExact laws.

This file deliberately does NOT implement another NLP semantics, reader,
admission service, or corpus ontology. In particular, SourceQueryLicence is
proof-relevant: the SLR JSON candidate producer cannot construct it merely
by returning a candidate or a string identifying a supposed review.

The later production weld must instantiate the model and discharge the
source-binding and interpretation-soundness obligations by independent,
checked evidence. An abstract proof under these premises is NOT a proof
that a particular article has been successfully interpreted.
-/
import RequestProject.Slr.Producer

namespace Wikidata
namespace Slr

universe uSource uReading uQuery uAnswer

/-- The existing SLR producer supplies observations; existing SLR/DASHI
    interpretation and consumer owners supply the actual semantic maps.
    The model is not an alternative interpretation engine. -/
structure DocumentQueryModel
    (Source : Type uSource) (Reading : Type uReading)
    (Query : Type uQuery) (Answer : Type uAnswer) where
  observe : Source → ProducerOutput
  live : ProducerOutput → Reading → Prop
  documentAnswer : Source → Query → Answer
  readingAnswer : Reading → Query → Answer

/-- A proof-bearing semantic licence for a PARTICULAR source and query.
    Distinct queries can require different resolution strength.
    'licencedAnswer' is the real, currently unfilled semantic correspondence;
    it cannot be inferred from parser output, QIDs, or a review-reference string.

    'closed' is consumer sufficiency on the live semantic fibre.
    No global unique reading is required. -/
structure SourceQueryLicence
    {Source : Type uSource} {Reading : Type uReading}
    {Query : Type uQuery} {Answer : Type uAnswer}
    (m : DocumentQueryModel Source Reading Query Answer)
    (source : Source) (query : Query) where
  observation : ProducerOutput
  sameProducedObservation : observation = m.observe source
  chosenReading : Reading
  chosenIsLive : m.live observation chosenReading
  licensedAnswer :
    m.documentAnswer source query = m.readingAnswer chosenReading query
  consumerClosed :
    ∀ reading, m.live observation reading →
      m.readingAnswer reading query = m.readingAnswer chosenReading query

/-- No semantic answer depends on the arbitrary choice of a still-live
    reading when the consumer is closed. -/
theorem liveReadingQueryInvariant
    {Source : Type uSource} {Reading : Type uReading}
    {Query : Type uQuery} {Answer : Type uAnswer}
    {m : DocumentQueryModel Source Reading Query Answer}
    {source : Source} {query : Query}
    (licence : SourceQueryLicence m source query)
    (reading : Reading)
    (live : m.live licence.observation reading) :
    m.readingAnswer reading query =
      m.readingAnswer licence.chosenReading query :=
  licence.consumerClosed reading live

/-- The original producer attachment is retained: a checked interpretation
    cannot silently substitute an unrelated observation at query time. -/
theorem licensedReadingBelongsToProducedObservation
    {Source : Type uSource} {Reading : Type uReading}
    {Query : Type uQuery} {Answer : Type uAnswer}
    {m : DocumentQueryModel Source Reading Query Answer}
    {source : Source} {query : Query}
    (licence : SourceQueryLicence m source query) :
    m.live (m.observe source) licence.chosenReading := by
  rw [← licence.sameProducedObservation]
  exact licence.chosenIsLive

/-- The end-to-end *general* theorem. The checked evaluator's answer must
    itself be justified against the selected reading; it is not accepted on
    the authority of a mere external success flag. -/
theorem slrJmdDocumentQuerySound
    {Source : Type uSource} {Reading : Type uReading}
    {Query : Type uQuery} {Answer : Type uAnswer}
    {m : DocumentQueryModel Source Reading Query Answer}
    {source : Source} {query : Query}
    (licence : SourceQueryLicence m source query)
    (answer : Answer)
    (checked : m.readingAnswer licence.chosenReading query = answer) :
    m.documentAnswer source query = answer :=
  licence.licensedAnswer.trans checked

/-- If a different reading remains live, a certified checked answer for it
    yields the SAME document answer. This is the actual consumer-relative
    adequacy law, not a requirement to resolve every ambiguity. -/
theorem slrJmdDocumentQuerySoundForAnyLiveReading
    {Source : Type uSource} {Reading : Type uReading}
    {Query : Type uQuery} {Answer : Type uAnswer}
    {m : DocumentQueryModel Source Reading Query Answer}
    {source : Source} {query : Query}
    (licence : SourceQueryLicence m source query)
    (reading : Reading)
    (live : m.live licence.observation reading)
    (answer : Answer)
    (checked : m.readingAnswer reading query = answer) :
    m.documentAnswer source query = answer :=
  licence.licensedAnswer.trans
    ((licence.consumerClosed reading live).symm.trans checked)

/-- An actual pair of still-live readings with different answers is
    a constructive negative gate: no query licence can be formed for this
    observation without further refinement or changing the query. This is the
    consumer-relative WrongType/non-factorability failure mode. -/
theorem incompatibleLiveReadingsBlockQueryLicence
    {Source : Type uSource} {Reading : Type uReading}
    {Query : Type uQuery} {Answer : Type uAnswer}
    {m : DocumentQueryModel Source Reading Query Answer}
    {source : Source} {query : Query}
    (left right : Reading)
    (leftLive : m.live (m.observe source) left)
    (rightLive : m.live (m.observe source) right)
    (disagree : m.readingAnswer left query ≠ m.readingAnswer right query) :
    ¬ SourceQueryLicence m source query := by
  intro licence
  have hl : m.live licence.observation left := by
    simpa [licence.sameProducedObservation] using leftLive
  have hr : m.live licence.observation right := by
    simpa [licence.sameProducedObservation] using rightLive
  exact disagree ((licence.consumerClosed left hl).trans
    (licence.consumerClosed right hr).symm)

/-- A smaller live fibre retains consumer closure, matching the generic
    DASHI semantic-refinement theorem. -/
theorem semanticClosurePreservedByRefinement
    {Observation : Type} {Reading : Type uReading}
    {Answer : Type uAnswer}
    (oldLive newLive : Observation → Reading → Prop)
    (consumer : Reading → Answer)
    (refines : ∀ o r, newLive o r → oldLive o r)
    (closed : ∀ o x y, oldLive o x → oldLive o y →
      consumer x = consumer y) :
    ∀ o x y, newLive o x → newLive o y →
      consumer x = consumer y := by
  intro o x y hx hy
  exact closed o x y (refines o x hx) (refines o y hy)


end Slr
end Wikidata
