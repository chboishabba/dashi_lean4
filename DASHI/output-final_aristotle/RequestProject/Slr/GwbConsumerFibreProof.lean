/-!
# GWB consumer-specific proof and explicit non-factorability witnesses

These finite examples instantiate the existing Agda consumer-relative closure,
typed eventual-fibre join, and source / account / occurrence firewalls.

The witnesses are *countermodels*, not historical claims. "Iraq possessed WMD"
is an independent WORLD axis; the Wikipedia sentence's reported claim is a
SOURCE axis. No flat parser label or Q207 identity may identify those axes.

SLR's native M12/S28 checker must independently pay source/parser identity.
These theorems only establish logical laws once the observed source
coordinates are supplied. They do not fabricate reviewed semantic licences.
-/
import RequestProject.Slr.DocumentQuerySound
import RequestProject.Slr.TemporalDocumentProof

namespace Wikidata
namespace Slr
namespace GwbConsumer

/- A provenance fibre joins ALL same-meaning execution annotations instead
   of keeping the last one. This is a law for the two independent
   fibre COORDINATES, not a new SLR producer or persistent representation. -/
structure EvidenceFibre (Meaning Meta : Type) where
  meanings : Meaning → Prop
  annotations : Meta → Prop

def EvidenceFibre.join {Meaning Meta : Type}
    (a b : EvidenceFibre Meaning Meta) : EvidenceFibre Meaning Meta :=
  ⟨(fun x => a.meanings x ∨ b.meanings x),
   (fun x => a.annotations x ∨ b.annotations x)⟩

theorem EvidenceFibre.extensional {Meaning Meta : Type}
    {a b : EvidenceFibre Meaning Meta}
    (hm : a.meanings = b.meanings)
    (ha : a.annotations = b.annotations) : a = b := by
  cases a with
  | mk am aa =>
    cases b with
    | mk bm ba =>
      cases hm
      cases ha
      rfl

theorem fibreJoinIdempotent {Meaning Meta : Type}
    (a : EvidenceFibre Meaning Meta) : a.join a = a := by
  apply EvidenceFibre.extensional
  · funext x
    exact propext (or_self (a.meanings x))
  · funext x
    exact propext (or_self (a.annotations x))

theorem fibreJoinCommutative {Meaning Meta : Type}
    (a b : EvidenceFibre Meaning Meta) : a.join b = b.join a := by
  apply EvidenceFibre.extensional
  · funext x
    exact propext (or_comm (a.meanings x) (b.meanings x))
  · funext x
    exact propext (or_comm (a.annotations x) (b.annotations x))

theorem fibreJoinAssociative {Meaning Meta : Type}
    (a b c : EvidenceFibre Meaning Meta) :
    (a.join b).join c = a.join (b.join c) := by
  apply EvidenceFibre.extensional
  · funext x
    exact propext (or_assoc (a.meanings x) (b.meanings x) (c.meanings x))
  · funext x
    exact propext (or_assoc (a.annotations x) (b.annotations x) (c.annotations x))

/-- All metadata alternatives remain available after either merge order. -/
theorem fibreJoinRetainsBothAnnotations {Meaning Meta : Type}
    (a b : EvidenceFibre Meaning Meta) (m : Meta)
    (left : a.annotations m) (right : b.annotations m) :
    (a.join b).annotations m ∧ (b.join a).annotations m :=
  ⟨Or.inl left, Or.inl right⟩

/-- The *source-visible* observation does not include independently decided
    world truth, actor referent, attachment of a date to an event, or
    subordinate-clause scope. Real SLR observations provide these axes only
    through the corresponding source-bound evidence and semantic review. -/
structure Observed where
  reportedPossessionClaim : Bool
  literalYear : Nat
  actorSurface : String
  flatScope : String
  deriving Repr, DecidableEq

structure Reading where
  observed : Observed
  worldPossession : Bool
  actorIsBush : Bool
  eventYear : Nat
  clauseEmbedded : Bool
  deriving Repr, DecidableEq

inductive ConsumerQuery
  | claimsReported | yearString2003 | actualPossession | actorIdentity
  | eventDated2003 | embeddedClause
  deriving Repr, DecidableEq

def answer (r : Reading) : ConsumerQuery → Bool
  | .claimsReported => r.observed.reportedPossessionClaim
  | .yearString2003 => decide (r.observed.literalYear = 2003)
  | .actualPossession => r.worldPossession
  | .actorIdentity => r.actorIsBush
  | .eventDated2003 => decide (r.eventYear = 2003)
  | .embeddedClause => r.clauseEmbedded

/-- The actual interpretation remains a LIVE reading fibre until review.
    Here a reading is live exactly when it agrees on the source-visible
    observation, deliberately leaving the other axes unconstrained. -/
def sourceModel : DocumentQueryModel
    Reading Observed Reading ConsumerQuery Bool where
  observe := Reading.observed
  live := fun o r => r.observed = o
  documentAnswer := answer
  readingAnswer := answer

/-- Even if world facts differ, the article-claim *mention* query is already
    sufficient. This constructs a real SourceQueryLicence for the syntactic
    consumer, discharging both nontrivial licence fields. -/
def reportedClaimLicence (source : Reading) :
    SourceQueryLicence sourceModel source .claimsReported where
  observation := source.observed
  sameProducedObservation := rfl
  chosenReading := source
  chosenIsLive := rfl
  consumerFactorises := by
    intro other h
    exact congrArg Observed.reportedPossessionClaim h
  consumerClosed := by
    intro other h
    exact congrArg Observed.reportedPossessionClaim h

/-- A year STRING query is source-sufficient without attaching that date
    to any event. -/
def yearStringLicence (source : Reading) :
    SourceQueryLicence sourceModel source .yearString2003 where
  observation := source.observed
  sameProducedObservation := rfl
  chosenReading := source
  chosenIsLive := rfl
  consumerFactorises := by
    intro other h
    exact congrArg (fun o : Observed => decide (o.literalYear = 2003)) h
  consumerClosed := by
    intro other h
    exact congrArg (fun o : Observed => decide (o.literalYear = 2003)) h

/-- Finite test state: the string, predicate and graph positions are pinned
    to observed GWB article wording, but the two semantic completions below
    are counterfactual possibilities, not historical claims. -/
def iraqArticleObservation : Observed :=
  { reportedPossessionClaim := true
    literalYear := 2003
    actorSurface := "He"
    flatScope := "unresolved-source-assertion" }

def readingA : Reading :=
  { observed := iraqArticleObservation
    worldPossession := true
    actorIsBush := true
    eventYear := 2003
    clauseEmbedded := true }

def readingB : Reading :=
  { observed := iraqArticleObservation
    worldPossession := false
    actorIsBush := false
    eventYear := 2004
    clauseEmbedded := false }

/-- Both counterfactual semantic completions produce THE SAME source
    observation; thus a source claim does not determine truth. -/
theorem competingReadingsSameSource :
    sourceModel.observe readingA = sourceModel.observe readingB := rfl

theorem sourceMentionQueryCloses :
    sourceModel.documentAnswer readingA .claimsReported = true :=
  slrJmdDocumentQuerySound (reportedClaimLicence readingA) true rfl

theorem literalYearQueryCloses :
    sourceModel.documentAnswer readingA .yearString2003 = true :=
  slrJmdDocumentQuerySound (yearStringLicence readingA) true rfl

/-- Exact nonfactorability witnesses for four distinct consumer needs.
    A source-text match alone cannot pay world occurrence, coreference,
    event-date attachment, or clause scope. -/
theorem actualPossessionNotLicensed :
    ¬ SourceQueryLicence sourceModel readingA .actualPossession := by
  apply incompatibleLiveReadingsBlockQueryLicence readingA readingB
  · rfl
  · rfl
  · decide

theorem actorIdentityNotLicensed :
    ¬ SourceQueryLicence sourceModel readingA .actorIdentity := by
  apply incompatibleLiveReadingsBlockQueryLicence readingA readingB
  · rfl
  · rfl
  · decide

theorem eventDateNotLicensed :
    ¬ SourceQueryLicence sourceModel readingA .eventDated2003 := by
  apply incompatibleLiveReadingsBlockQueryLicence readingA readingB
  · rfl
  · rfl
  · decide

theorem embeddedScopeNotLicensed :
    ¬ SourceQueryLicence sourceModel readingA .embeddedClause := by
  apply incompatibleLiveReadingsBlockQueryLicence readingA readingB
  · rfl
  · rfl
  · decide

/-- S28 scope-indexed transitivity can close an account-relative order
    without leaking it into a differently attributed scope. -/
theorem scopedTimelineClosure
    {Scope Event : Type} (direct : Scope → Event → Event → Prop)
    (account : Scope) (a b c : Event)
    (ab : ScopedOrderReachable direct account a b)
    (bc : ScopedOrderReachable direct account b c) :
    ScopedOrderReachable direct account a c :=
  scopedTemporalOrderClosureSound direct account a b c ab bc

end GwbConsumer
end Slr
end Wikidata
