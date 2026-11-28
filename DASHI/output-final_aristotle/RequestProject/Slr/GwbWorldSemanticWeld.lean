import RequestProject.Slr.WorldSemanticFibre
import RequestProject.Slr.GwbArticleSystemSoundness

/-! Exact bounded port of the existing archived-clause semantics.
No unrestricted English coverage, world identity, or native predicate
attachment is inferred by this conversion. -/
namespace Wikidata.Slr.GwbWorldSemanticWeld

open GwbArticleSystem WorldSemanticFibre

def localActor (c : AttributedClause) : Referent :=
  if c.actor = "tax cut" then .eventuality c.actor else .entity c.actor

def clauseRole (c : AttributedClause) : Role :=
  if c.scope = "patient; agent unspecified" then .patient
  else if c.scope = "asserted reporting act" then .speaker
  else .agent

def clauseScope (c : AttributedClause) : Scope :=
  if c.scope = "asserted" ∨ c.scope = "asserted reporting act" ∨
    c.scope = "patient; agent unspecified" then .asserted
  else if c.scope = "reported prediction by Bush" then .predicted
  else .unknown

def clauseReading (a : Anchor) (c : AttributedClause) : Reading :=
  { anchor := a
    referent := localActor c
    role := clauseRole c
    scope := clauseScope c
    sign := .positive
    event := c.predicate ++ ":" ++ c.object
    capacity := if c.capacity = "" then none else some c.capacity
    time := c.year.map toString
    attribution := if c.scope = "reported prediction by Bush" then some "Bush" else none }

def typedClaims (a : Anchor) (rule : ArchivedClauseRule) : List Reading :=
  (ruleClaims rule).map (clauseReading a)

def typedAnswer (a : Anchor) (article : String) (rule : ArchivedClauseRule) :
    Option (List Reading) :=
  (archivedClauseAnswer article rule).map (List.map (clauseReading a))

theorem typedAnswerExact (a : Anchor) (article : String) (rule : ArchivedClauseRule)
    (matched : archivedClauseMatches article rule = true) :
    typedAnswer a article rule = some (typedClaims a rule) := by
  simp [typedAnswer, archivedClauseAnswer, matched, typedClaims]

def bushActions (a : Anchor) (rule : ArchivedClauseRule) : List Reading :=
  (typedClaims a rule).filter (fun r => action (.entity "Bush") r == .positive)

def testAnchor : Anchor := ⟨"bounded-specimen","not-a-native-digest","clause","unattached"⟩

theorem coordinatedFour : (bushActions testAnchor .governor).length = 4 := by decide
theorem passiveZero : (bushActions testAnchor .suspension).length = 0 := by decide
theorem reportingOne : (bushActions testAnchor .taxStatements).length = 1 := by decide

/-- Source-local interpretation is inherited from the original controlled
    clause model. Native binding must separately establish the anchor. -/
def typedModel (a : Anchor) :
    DocumentQueryModel String String ArchivedClauseReading ArchivedClauseRule
      (Option (List Reading)) where
  observe := id
  live := fun o r => r.original = o
  documentAnswer := typedAnswer a
  readingAnswer := fun r q => typedAnswer a r.original q

def typedLicence (a : Anchor) (article : String) (rule : ArchivedClauseRule) :
    SourceQueryLicence (typedModel a) article rule where
  observation := article
  sameProducedObservation := rfl
  chosenReading := ⟨article, Lean.Json.null⟩
  chosenIsLive := rfl
  consumerFactorises := by
    intro s h
    exact congrArg (fun t => typedAnswer a t rule) h
  consumerClosed := by
    intro r h
    exact congrArg (fun t => typedAnswer a t rule) h

theorem typedSourceSound
    {article : String} {slr projection root : Lean.Json}
    (source : GwbArticleIdentity.CheckedGwbRootIdentity article slr projection root)
    (a : Anchor) (rule : ArchivedClauseRule)
    (matched : archivedClauseMatches article rule = true) :
    GwbArticleIdentity.checkGwbRootIdentity article slr projection root = true ∧
    (typedModel a).documentAnswer article rule = some (typedClaims a rule) := by
  exact ⟨source.checked, typedAnswerExact a article rule matched⟩

/-- The source coordinate inverse must be supplied for each individual claim,
    not merely one shared clause anchor. The attachment is proof-relevant. -/
structure AttachedClaim (article : String) (rule : ArchivedClauseRule) where
  clause : AttributedClause
  member : clause ∈ ruleClaims rule
  matched : archivedClauseMatches article rule = true
  anchor : Anchor
  predicateStart : Nat
  predicateEnd : Nat
  spanNonempty : predicateStart < predicateEnd
  spanWithin : (ruleSpan rule).1 ≤ predicateStart ∧ predicateEnd ≤ (ruleSpan rule).2
  originalLiteral : String
  literalExact : String.ofList ((article.toList.drop predicateStart).take
    (predicateEnd - predicateStart)) = originalLiteral

def AttachedClaim.reading {article : String} {rule : ArchivedClauseRule}
    (c : AttachedClaim article rule) : Reading :=
  clauseReading c.anchor c.clause

theorem attachedSourceInverse {article : String} {rule : ArchivedClauseRule}
    (c : AttachedClaim article rule) :
    c.reading.anchor = c.anchor ∧ c.clause ∈ ruleClaims rule ∧
    String.ofList ((article.toList.drop c.predicateStart).take
      (c.predicateEnd - c.predicateStart)) = c.originalLiteral :=
  ⟨rfl, c.member, c.literalExact⟩

/-- Exact predicate occurrences for the bounded original rules, in claim order.
These are source coordinates, not a parser-dependent token allocation. -/
def predicateOccurrences : ArchivedClauseRule → List (Nat × Nat × String)
  | .governor => [(898, 907, "sponsored"), (933, 942, "increased"), (966, 969, "set"), (1004, 1012, "reformed")]
  | .suspension => [(6828, 6837, "suspended")]
  | .taxStatements => [(18684, 18690, "warned"), (18715, 18721, "stated"), (18743, 18752, "stimulate"), (18769, 18775, "create")]

def occurrenceMatches (article : String) (p : Nat × Nat × String) : Bool :=
  decide (p.1 < p.2.1 ∧ p.2.1 ≤ article.toList.length) &&
    String.ofList ((article.toList.drop p.1).take (p.2.1-p.1)) == p.2.2

def checkedOccurrences (article : String) (rule : ArchivedClauseRule) : Bool :=
  archivedClauseMatches article rule &&
    decide ((predicateOccurrences rule).length = (ruleClaims rule).length) &&
    (predicateOccurrences rule).all (occurrenceMatches article)

theorem occurrenceCount (rule : ArchivedClauseRule) :
    (predicateOccurrences rule).length = (ruleClaims rule).length := by
  cases rule <;> decide

def indexedClaims (rule : ArchivedClauseRule) :=
  (ruleClaims rule).zip (predicateOccurrences rule)

theorem indexedClaimCount (rule : ArchivedClauseRule) :
    (indexedClaims rule).length = (ruleClaims rule).length := by
  cases rule <;> decide

/-- Native attachment is not obtained merely by choosing a subspan.
The claim and occurrence must belong to the same indexed rule row. -/
structure IndexedAttachedClaim (article : String) (rule : ArchivedClauseRule) where
  claim : AttributedClause
  occurrence : Nat × Nat × String
  paired : (claim, occurrence) ∈ indexedClaims rule
  originalMatched : checkedOccurrences article rule = true
  literalMatched : occurrenceMatches article occurrence = true
  anchor : Anchor

def IndexedAttachedClaim.reading {article : String} {rule : ArchivedClauseRule}
    (c : IndexedAttachedClaim article rule) : Reading :=
  clauseReading c.anchor c.claim

theorem indexedAttachmentRetainsPair {article : String} {rule : ArchivedClauseRule}
    (c : IndexedAttachedClaim article rule) :
    (c.claim, c.occurrence) ∈ indexedClaims rule ∧
    occurrenceMatches article c.occurrence = true :=
  ⟨c.paired, c.literalMatched⟩

end Wikidata.Slr.GwbWorldSemanticWeld

#print axioms Wikidata.Slr.GwbWorldSemanticWeld.typedSourceSound
#print axioms Wikidata.Slr.GwbWorldSemanticWeld.attachedSourceInverse
