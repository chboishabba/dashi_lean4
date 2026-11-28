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

end Wikidata.Slr.GwbWorldSemanticWeld

#print axioms Wikidata.Slr.GwbWorldSemanticWeld.typedSourceSound
#print axioms Wikidata.Slr.GwbWorldSemanticWeld.attachedSourceInverse
