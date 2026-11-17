import RequestProject.Slr.DocumentQuerySound

/-!
# Generic temporal and event query laws over source-licensed SLR readings

This is a theorem-only bridge. It reuses existing world owners:
  DASHI/Cognition/PNF/SensibLawSemanticStatusProductExact.agda
  DASHI/Cognition/PNF/SensibLawChronologyContestationSpineExact.agda
  DASHI/Cognition/PNF/SensibLawPersistentStatementObservationEventSpineExact.agda
  DASHI/Cognition/PNF/SentenceParagraphNaturalDeltaExact.agda
  DASHI/Core/ConsumerDescentMinimalObserverExact.agda

No new event ontology, parser, or temporal interpretation rules are defined.
Source observations still require the actual producer-to-semantics licence.
The context parameter of an ordering relation is mandatory; no inference
may merge speaker beliefs, narrator assertions or external-world admission.
-/

namespace Wikidata
namespace Slr

universe uEvent uScope uEvidence uSource uObservation uReading uQuery uAnswer

/-- Reachability of licensed event-order evidence inside one context.
    An edge requires independent semantic licensing at the calling boundary;
    Relation.TransGen is Lean's existing transitive-closure owner. -/
def ScopedOrderReachable
    {Scope : Type uScope} {Event : Type uEvent}
    (direct : Scope → Event → Event → Prop)
    (context : Scope) (left right : Event) : Prop :=
  Relation.TransGen (direct context) left right

/-- A direct licensed temporal assertion is one path step. -/
theorem licensedTemporalAssertionSound
    {Scope : Type uScope} {Event : Type uEvent}
    (direct : Scope → Event → Event → Prop)
    (context : Scope) (left right : Event)
    (h : direct context left right) :
    ScopedOrderReachable direct context left right :=
  Relation.TransGen.single h

/-- Source-relative temporal closure does not cross contexts:
    its two premises share the SAME context index. -/
theorem scopedTemporalOrderClosureSound
    {Scope : Type uScope} {Event : Type uEvent}
    (direct : Scope → Event → Event → Prop)
    (context : Scope) (first middle last : Event)
    (h1 : ScopedOrderReachable direct context first middle)
    (h2 : ScopedOrderReachable direct context middle last) :
    ScopedOrderReachable direct context first last :=
  Relation.TransGen.trans h1 h2

/-- A strict temporal reading additionally needs a cycle-free assumption.
    Bare graph reachability is not proof of a consistent strict chronology. -/
def ContextAcyclic
    {Scope : Type uScope} {Event : Type uEvent}
    (direct : Scope → Event → Event → Prop) (context : Scope) : Prop :=
  ∀ event, ¬ ScopedOrderReachable direct context event event

theorem acceptedChronologyHasNoSelfPrecedence
    {Scope : Type uScope} {Event : Type uEvent}
    (direct : Scope → Event → Event → Prop) (context : Scope)
    (acyclic : ContextAcyclic direct context) (event : Event) :
    ¬ ScopedOrderReachable direct context event event :=
  acyclic event

/-- It is logically invalid to infer another scope's relation from the
    existence of an edge in the first scope without scope transport. -/
theorem sourceOrderDoesNotAutomaticallyBecomeWorldOrder :
    ¬ (∀ (Scope Event : Type) (direct : Scope → Event → Event → Prop)
          (c₁ c₂ : Scope) (a b : Event),
          direct c₁ a b → direct c₂ a b) := by
  intro h
  have contradiction : false = true :=
    h Bool Unit (fun c _ _ => c = true) true false () () rfl
  cases contradiction

/-- Source position is a different relation from narrated event order. -/
theorem textOrderDoesNotEntailEventOrder :
    ¬ (∀ (Event : Type) (sourcePosition narratedBefore : Event → Event → Prop)
          (a b : Event), sourcePosition a b → narratedBefore a b) := by
  intro h
  have contradiction : False :=
    h Bool (fun a b => a = true ∧ b = false)
      (fun _ _ => False) true false ⟨rfl, rfl⟩
  exact contradiction

/-- Identical names, dates or QIDs do not by themselves prove
    identity of two narrative events. -/
theorem commonLabelDoesNotEstablishEventIdentity :
    ¬ (∀ {Event : Type} (label : Event → String)
          (a b : Event), label a = label b → a = b) := by
  intro h
  have contradiction : true = false :=
    h (fun _ : Bool => "same label") true false rfl
  cases contradiction

/-- Abstract evidence-preservation law for an append-only source history.
    It is not a current-belief or truth-maintenance rule. -/
theorem temporalCorrectionPreservesHistory
    {Evidence : Type uEvidence}
    (prior addition : List Evidence) (item : Evidence)
    (recorded : item ∈ prior) :
    item ∈ prior ++ addition := by
  simp only [List.mem_append]
  exact Or.inl recorded

/-- Sentence-to-paragraph-to-page grouping does not change the sequence of
    retained evidence. Semantic fusion requires the separate naturality
    proof of SentenceParagraphNaturalDeltaExact, not this associativity alone. -/
theorem temporalEvidenceFusionAssociative
    {Evidence : Type uEvidence}
    (sentences paragraph page : List Evidence) :
    (sentences ++ paragraph) ++ page =
      sentences ++ (paragraph ++ page) := by
  simp only [List.append_assoc]

/-- The existing generic L6 theorem is instantiated unchanged for all
    temporal/event queries whose licensed readings supply a checked answer.
    Neither sentence order nor the parser candidate alone supplies a licence. -/
theorem temporalQueryFactorsThroughDocument
    {Source : Type uSource} {Observation : Type uObservation}
    {Reading : Type uReading}
    {Query : Type uQuery} {Answer : Type uAnswer}
    {m : DocumentQueryModel Source Observation Reading Query Answer}
    {source : Source} {query : Query}
    (licence : SourceQueryLicence m source query)
    (answer : Answer)
    (checked : m.readingAnswer licence.chosenReading query = answer) :
    m.documentAnswer source query = answer :=
  slrJmdDocumentQuerySound licence answer checked

end Slr
end Wikidata
