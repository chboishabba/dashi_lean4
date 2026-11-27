import RequestProject.Slr.GwbArticleIdentity
import RequestProject.Slr.GwbHyperfabricTransport
import RequestProject.Slr.GwbProofComposition
import RequestProject.Slr.GwbWorldGraphProof

/-!
GWB article-local end-to-end proof-composition theorem.

It depends on:
  * the original exact Q207 article/SLR parser and JMD sitelink checker;
  * the same original source-checked native Rust semantic receipt;
  * a fragment that is provably drawn from that checked source;
  * a query-specific SourceQueryLicence over the ACTUAL typed row list;
  * an independently JMD-checked KB property statement.

A successful theorem proves the stated properties of those checked inputs.
It does NOT manufacture the externally missing semantic coverage,
cross-sentence referent identity, event occurrence or statement-to-prose
alignment. Those are not implicit in the source, graph or checker flags.
-/

namespace Wikidata
namespace Slr
namespace GwbArticleSystem

open Lean
open GwbTypedFibre

/-- This is the exact dependency interface the automatic GWB elaborator
must inhabit. A semantic consumer may use only a source observation
that is explicitly the typed list from the original checked receipt. -/
theorem checkedArticleLocalSystemSound
    {article : String} {slr projection native wikidata : Json}
    (root : GwbArticleIdentity.CheckedGwbRootIdentity
      article slr projection wikidata)
    (source : CheckedRows article slr projection native)
    (fragment : GwbHyperfabric.Fragment source)
    {Observation Reading Query Answer : Type}
    (model : DocumentQueryModel
      (List SentenceObservation) Observation Reading Query Answer)
    (query : Query)
    (licence : SourceQueryLicence model source.rows.toList query)
    (answerValue : Answer)
    (evaluation :
      model.readingAnswer licence.chosenReading query = answerValue) :
    GwbArticleIdentity.checkGwbRootIdentity
      article slr projection wikidata = true ∧
    GwbNativeFibre.checkRealGwbNativeFibreReceipt
      article slr projection native = true ∧
    model.documentAnswer source.rows.toList query = answerValue := by
  exact ⟨GwbArticleIdentity.checkedGwbRootSourceAndSitelink root,
    GwbHyperfabric.anyFragmentRetainsOriginalReceipt fragment,
    slrJmdDocumentQuerySound licence answerValue evaluation⟩

/-- Explicitly compose the article-relative theorem with ONE separately
reimported JMD property, requiring its QID subject to be the same Q207
root. This does not assert the historical truth of the property or
automatically identify a source sentence with the KB statement. -/
theorem checkedArticleAndRootKBPropertySound
    {article : String} {slr projection native wikidata : Json}
    (root : GwbArticleIdentity.CheckedGwbRootIdentity
      article slr projection wikidata)
    (source : CheckedRows article slr projection native)
    (fragment : GwbHyperfabric.Fragment source)
    {Observation Reading Query Answer : Type}
    (model : DocumentQueryModel
      (List SentenceObservation) Observation Reading Query Answer)
    (query : Query)
    (licence : SourceQueryLicence model source.rows.toList query)
    (answerValue : Answer)
    (evaluation :
      model.readingAnswer licence.chosenReading query = answerValue)
    (property : GwbWorldGraph.CheckedWorldProperty)
    (sameQid : property.subject = Qid.wd "Q207") :
    GwbArticleIdentity.checkGwbRootIdentity
      article slr projection wikidata = true ∧
    GwbNativeFibre.checkRealGwbNativeFibreReceipt
      article slr projection native = true ∧
    model.documentAnswer source.rows.toList query = answerValue ∧
    (∃ p, (p, Qid.wd "Q207", property.object) ∈
      property.pkb.stmts ∧
      property.pkb.isSubPropertyOf p property.property = true) := by
  have articleProof :=
    checkedArticleLocalSystemSound root source fragment
      model query licence answerValue evaluation
  have kbProof := GwbWorldGraph.checkedWorldPropertySound property
  rcases articleProof with ⟨hIdentity, hSource, hAnswer⟩
  rw [sameQid] at kbProof
  exact ⟨hIdentity, hSource, hAnswer, kbProof⟩

/- The canonical article lead is a bounded controlled-language specimen,
not an unrestricted English-to-Wikidata translator. The exact source
sentence explicitly attributes the office to the named article subject.
The JMD sitelink binds that subject to Q207; independent EntityData must
support P39/Q11696. The article's date and ordinal are NOT mapped to
Wikidata qualifiers by this rule. -/

def officeLead : String :=
  "George Walker Bush (born July 6, 1946) is an American retired politician and businessman who served as the 43rd president of the United States from 2001 to 2009."

def officeClaim (article : String) : Bool :=
  article.startsWith officeLead

private def entityRecord (json : Json) (qid : String) : Json :=
  (((json.getObjVal? "entities").toOption.getD Json.null).getObjVal? qid).toOption.getD Json.null

def entityRevision (json : Json) (qid : String) : Option Nat :=
  ((entityRecord json qid).getObjValAs? Nat "lastrevid").toOption

def officeLabelChecked (office : Json) : Bool :=
  GwbWorldGraph.jsonEntityMatchesQid "Q11696" office &&
  Cli.entityLabelIn (entityRecord office "Q11696") "en" ==
    some "President of the United States"

def officePKB (root office : Json) : PKB :=
  GwbWorldGraph.pkbFromImportedEntities
    (Cli.entitiesOfJson root ++ Cli.entitiesOfJson office)

def officePropertySupported (root office : Json) : Bool :=
  (officePKB root office).supportsB (Pid.wd "P39")
    (Qid.wd "Q207") (Qid.wd "Q11696")

/-- The source rule and independent KB support are retained as distinct
    premises. This is an article-claim/KB agreement under the named bounded
    rule, not general semantic identity, qualifier agreement or world truth. -/
theorem checkedOfficeClaimAndKB
    {article : String} {slr projection root office : Json}
    (source : GwbArticleIdentity.CheckedGwbRootIdentity article slr projection root)
    (claim : officeClaim article = true)
    (label : officeLabelChecked office = true)
    (support : officePropertySupported root office = true) :
    GwbArticleIdentity.checkGwbRootIdentity article slr projection root = true ∧
    officeClaim article = true ∧ officeLabelChecked office = true ∧
    (∃ p, (p, Qid.wd "Q207", Qid.wd "Q11696") ∈ (officePKB root office).stmts ∧
      (officePKB root office).isSubPropertyOf p (Pid.wd "P39") = true) := by
  exact ⟨source.checked, claim, label, PKB.supportsB_iff.mp support⟩

/-- Extend the EXISTING exact bounded lead rule, not a generic parser.
Its selected consumer is the office interval at year granularity. Each
matched native statement carries its complete GUID, rank and qualifiers;
other qualifier semantics remain outside this consumer. -/
theorem checkedOfficeClaimAndQualifiedYears
    {article : String} {slr projection root office statement : Json}
    (source : GwbArticleIdentity.CheckedGwbRootIdentity article slr projection root)
    (claim : officeClaim article = true)
    (label : officeLabelChecked office = true)
    (support : officePropertySupported root office = true)
    (years : statement ∈ GwbWorldGraph.qualifiedYearRows root "Q207" "P39" "Q11696" 2001 2009) :
    officeClaim article = true ∧
    (∃ p, (p, Qid.wd "Q207", Qid.wd "Q11696") ∈ (officePKB root office).stmts ∧
      (officePKB root office).isSubPropertyOf p (Pid.wd "P39") = true) ∧
    statement ∈ GwbWorldGraph.originalPropertyRows root "Q207" "P39" ∧
    GwbWorldGraph.yearIntervalStatementMatches "P39" "Q11696" 2001 2009 statement = true := by
  have base := checkedOfficeClaimAndKB source claim label support
  have native := (GwbWorldGraph.qualifiedYearRowsExact root "Q207" "P39" "Q11696" 2001 2009 statement).mp years
  exact ⟨claim, base.2.2.2, native.1, native.2⟩

/-- Bounded interpretation of exact archived clauses. The semantic unit is
the explicit attributed proposition, not a claim of historical occurrence.
A surname is source-local here; only the independent root lead rule maps Q207.
No closed-world conclusion follows from a missing clause. -/
structure AttributedClause where
  actor : String
  predicate : String
  object : String
  capacity : String
  scope : String
  year : Option Nat
  deriving Repr, DecidableEq

def clauseJson (c : AttributedClause) : Json :=
  Json.mkObj [("actor", toJson c.actor), ("predicate", toJson c.predicate),
    ("object", toJson c.object), ("capacity", toJson c.capacity),
    ("scope", toJson c.scope), ("year", toJson c.year)]

inductive ArchivedClauseRule where
  | governor | suspension | taxStatements
  deriving Repr, DecidableEq

def ruleLiteral : ArchivedClauseRule → String
  | .governor => "As governor , Bush sponsored tort reform legislation, increased funding for education, set higher standards for schools, and reformed the criminal justice system."
  | .suspension => "In 1972, Bush was suspended from flying for failure to take a scheduled physical exam."
  | .taxStatements => "Federal Reserve chairman Alan Greenspan warned of a recession and Bush stated that a tax cut would stimulate the economy and create jobs."

def ruleSpan : ArchivedClauseRule → Nat × Nat
  | .governor => (879, 1041)
  | .suspension => (6810, 6896)
  | .taxStatements => (18644, 18781)

def ruleClaims : ArchivedClauseRule → List AttributedClause
  | .governor =>
    [⟨"Bush", "sponsor", "tort reform legislation", "governor", "asserted", none⟩,
     ⟨"Bush", "increase", "funding for education", "governor", "asserted", none⟩,
     ⟨"Bush", "set", "higher standards for schools", "governor", "asserted", none⟩,
     ⟨"Bush", "reform", "criminal justice system", "governor", "asserted", none⟩]
  | .suspension =>
    [⟨"Bush", "be suspended", "from flying", "", "patient; agent unspecified", some 1972⟩]
  | .taxStatements =>
    [⟨"Alan Greenspan", "warn", "of a recession", "Federal Reserve chairman", "asserted reporting act", none⟩,
     ⟨"Bush", "state", "tax cut would stimulate the economy and create jobs", "", "asserted reporting act", none⟩,
     ⟨"tax cut", "stimulate", "economy", "", "reported prediction by Bush", none⟩,
     ⟨"tax cut", "create", "jobs", "", "reported prediction by Bush", none⟩]

def archivedClauseMatches (article : String) (rule : ArchivedClauseRule) : Bool :=
  let (a, b) := ruleSpan rule
  decide (b ≤ article.toList.length) &&
  String.ofList ((article.toList.drop a).take (b-a)) == ruleLiteral rule

/-- This model interprets only the explicitly specified controlled clauses.
Other readings may differ on any unrelated information, including the
world identity of the surname. A nonmatching rule has no positive answer. -/
def archivedClauseAnswer (article : String) (rule : ArchivedClauseRule) :
    Option (List AttributedClause) :=
  if archivedClauseMatches article rule then some (ruleClaims rule) else none

structure ArchivedClauseReading where
  original : String
  otherInterpretation : Json

def archivedClauseModel : DocumentQueryModel String String ArchivedClauseReading
    ArchivedClauseRule (Option (List AttributedClause)) where
  observe := id
  live := fun o r => r.original = o
  documentAnswer := archivedClauseAnswer
  readingAnswer := fun r => archivedClauseAnswer r.original

def archivedClauseLicence (article : String) (rule : ArchivedClauseRule) :
    SourceQueryLicence archivedClauseModel article rule where
  observation := article
  sameProducedObservation := rfl
  chosenReading := ⟨article, Json.null⟩
  chosenIsLive := rfl
  consumerFactorises := by
    intro s h
    exact congrArg (fun t => archivedClauseAnswer t rule) h
  consumerClosed := by
    intro reading h
    exact congrArg (fun t => archivedClauseAnswer t rule) h

theorem checkedArchivedClauseSound
    {article : String} {slr projection root : Json}
    (source : GwbArticleIdentity.CheckedGwbRootIdentity article slr projection root)
    (rule : ArchivedClauseRule)
    (matched : archivedClauseMatches article rule = true) :
    GwbArticleIdentity.checkGwbRootIdentity article slr projection root = true ∧
      archivedClauseModel.documentAnswer article rule = some (ruleClaims rule) := by
  refine ⟨source.checked, slrJmdDocumentQuerySound (archivedClauseLicence article rule) _ ?_⟩
  change archivedClauseAnswer article rule = some (ruleClaims rule)
  simp [archivedClauseAnswer, matched]

/-- A passive patient and reported prediction cannot be promoted by these
bounded rules into an asserted action by the named subject. -/
def assertedAction (actor : String) (c : AttributedClause) : Bool :=
  c.actor == actor && (c.scope == "asserted" || c.scope == "asserted reporting act")

theorem suspensionIsNotBushAction :
    (ruleClaims .suspension).filter (assertedAction "Bush") = [] := by decide

theorem predictionIsNotBushAction :
    ((ruleClaims .taxStatements).filter (assertedAction "Bush")).length = 1 := by decide

theorem governorCoordinatedActions :
    ((ruleClaims .governor).filter (assertedAction "Bush")).length = 4 := by decide


/-- The two offices have the same independently checked object but different
holders and intervals. The GHWB template is a fail-closed controlled lead:
it must be matched against the original acquired article, not assumed present. -/
inductive BushOfficeSubject where
  | son | father
  deriving DecidableEq, Repr

def officeSubjectQid : BushOfficeSubject → String
  | .son => "Q207"
  | .father => "Q23505"

def officeSubjectTitle : BushOfficeSubject → String
  | .son => "George W. Bush"
  | .father => "George H. W. Bush"

def officeSubjectYears : BushOfficeSubject → Nat × Nat
  | .son => (2001, 2009)
  | .father => (1989, 1993)

def officeSubjectLead : BushOfficeSubject → String
  | .son => officeLead
  | .father => "George Herbert Walker Bush (June 12, 1924 – November 30, 2018) was an American politician and statesman who served as the 41st president of the United States from 1989 to 1993."

/-- Current public GHWB lead is shorter than the historical template.
Keep both explicitly declared forms; no approximate textual match. -/
def officeLeadVariants (subject : BushOfficeSubject) : List String :=
  match subject with
  | .son => [officeLead]
  | .father =>
    let old := officeSubjectLead .father
    let current := old.replace "an American politician and statesman who served as " ""
    [old, current, current.replace " – " " – "]

def matchedOfficeLead? (subject : BushOfficeSubject) (article : String) : Option String :=
  (officeLeadVariants subject).find? (fun literal => article.startsWith literal)

def indexedOfficeLeadMatches (subject : BushOfficeSubject) (article : String) : Bool :=
  (matchedOfficeLead? subject article).isSome

/-- Exact controlled source interpretation. Unknown lead formats have no
positive answer; do not extrapolate to other article claims. -/
def indexedOfficeAnswer (article : String) (subject : BushOfficeSubject) :
    Option (String × String × String × Nat × Nat) :=
  if indexedOfficeLeadMatches subject article then
    some (officeSubjectQid subject, "P39", "Q11696",
      (officeSubjectYears subject).1, (officeSubjectYears subject).2)
  else none

def indexedOfficeModel : DocumentQueryModel String String String BushOfficeSubject
    (Option (String × String × String × Nat × Nat)) where
  observe := id
  live := fun o r => r = o
  documentAnswer := indexedOfficeAnswer
  readingAnswer := indexedOfficeAnswer

def indexedOfficeLicence (article : String) (subject : BushOfficeSubject) :
    SourceQueryLicence indexedOfficeModel article subject where
  observation := article
  sameProducedObservation := rfl
  chosenReading := article
  chosenIsLive := rfl
  consumerFactorises := by
    intro s h
    exact congrArg (fun t => indexedOfficeAnswer t subject) h
  consumerClosed := by
    intro reading h
    exact congrArg (fun t => indexedOfficeAnswer t subject) h

def indexedOfficeRootCheck (subject : BushOfficeSubject) (article : String)
    (slr projection entity : Json) : Bool :=
  let revision := (slr.getObjValAs? String "revision_ref").toOption.getD ""
  let unit := (slr.getObjValAs? String "source_unit_ref").toOption.getD ""
  ArticleProof.checkProjectionFor (officeSubjectQid subject) article slr projection &&
    revision.startsWith "enwiki-revid:" &&
    (match (revision.drop "enwiki-revid:".length).toString.toNat? with
     | some n => decide (n > 0) && unit == ("wikipedia:en:" ++
         (officeSubjectTitle subject).replace " " "_" ++ ":" ++ toString n)
     | none => false) &&
    GwbArticleIdentity.checkSitelink (officeSubjectQid subject) (officeSubjectTitle subject) entity &&
    GwbWorldGraph.jsonEntityMatchesQid (officeSubjectQid subject) entity

theorem indexedOfficeAnswerSound (subject : BushOfficeSubject) (article : String)
    (matched : indexedOfficeLeadMatches subject article = true) :
    indexedOfficeModel.documentAnswer article subject =
      some (officeSubjectQid subject, "P39", "Q11696",
        (officeSubjectYears subject).1, (officeSubjectYears subject).2) := by
  apply slrJmdDocumentQuerySound (indexedOfficeLicence article subject)
  change indexedOfficeAnswer article subject = _
  simp [indexedOfficeAnswer, matched]

theorem bushOfficeIntervalsDisjoint :
    (officeSubjectYears .father).2 < (officeSubjectYears .son).1 := by decide

theorem distinctBushOfficeHolders :
    officeSubjectQid .father ≠ officeSubjectQid .son := by decide

/-- Reuse original JMD qualified-year evidence on both roots, and compose the
licensed office answers in both directions. This is a comparison of separate
tenures in the same office, NOT direct succession or a shared event. -/
theorem reciprocalBushOfficeSound
    {son father : String}
    (hs : indexedOfficeLeadMatches .son son = true)
    (hf : indexedOfficeLeadMatches .father father = true) :
    (indexedOfficeModel.documentAnswer son .son, indexedOfficeModel.documentAnswer father .father) =
      (some ("Q207", "P39", "Q11696", 2001, 2009),
       some ("Q23505", "P39", "Q11696", 1989, 1993)) ∧
    (officeSubjectYears .father).2 < (officeSubjectYears .son).1 := by
  constructor
  · rw [indexedOfficeAnswerSound .son son hs, indexedOfficeAnswerSound .father father hf] <;> rfl
  · exact bushOfficeIntervalsDisjoint


/-- A bounded shared-event key, independent of article subject. The
    historical result is only source-attributed; neither its legitimacy nor
    the constitutional/legal consequences are inferred. -/
structure ElectionClaim where
  eventKey : String
  winner : String
  opponentName : String
  year : Nat
  deriving DecidableEq, Repr

def election2000 : ElectionClaim :=
  ⟨"us-presidential-election:2000", "Q207", "Al Gore", 2000⟩

private def eventNat (j : Json) (k : String) : Option Nat :=
  (j.getObjValAs? Nat k).toOption

private def eventString (j : Json) (k : String) : String :=
  (j.getObjValAs? String k).toOption.getD ""

private def eventObj (j : Json) (k : String) : Json :=
  (j.getObjVal? k).toOption.getD Json.null

private def eventArray (j : Json) (k : String) : List Json :=
  ((j.getObjValAs? (Array Json) k).toOption.getD #[]).toList

/-- Match the explicit source clause, not a generic string similarity.
    Require the independently checked source projection and the original
    defeat predicate with its own direct syntactic subject/object. The GWB
    pronoun rule is restricted to the original lead's known sentence span.
    GHWB must have an explicit named subject, never inherited article topic. -/
def electionRowMatches (subject : BushOfficeSubject) (article : String) (row : Json) : Bool :=
  match eventNat row "sentence_start", eventNat row "sentence_end" with
  | some start, some stop =>
    let literal := String.ofList ((article.toList.drop start).take (stop-start))
    let normalized := (literal.replace " ," ",").replace " ." "."
    let pred := eventObj row "predicate"
    let actors := eventArray row "actors"
    let patients := eventArray row "patients"
    let subjectLabel := match subject with | .son => "he" | .father => "Bush"
    let clause := match subject with
      | .son => start == 1141 && stop == 1377 &&
          normalized.startsWith ("In the 2000 presidential election, he defeated " ++
            "Democratic incumbent vice president Al Gore")
      | .father => normalized.startsWith ("George W. Bush defeated Al Gore " ++
          "in the 2000 election") &&
          normalized.endsWith "."
    decide (start < stop ∧ stop ≤ article.toList.length) &&
      clause && eventString pred "lemma" == "defeat" &&
      actors.any (fun a => eventString a "surface" == subjectLabel &&
        eventString a "dep" == "nsubj") &&
      patients.any (fun p => eventString p "surface" == "Gore" &&
        eventString p "dep" == "dobj") &&
      (row.getObjValAs? Bool "negation_dependency_candidate").toOption == some false
  | _, _ => false

def electionRows (subject : BushOfficeSubject) (article : String) (projection : Json) : List Json :=
  (eventArray projection "event_candidates").filter (electionRowMatches subject article)

theorem electionRowsExact (subject : BushOfficeSubject) (article : String)
    (projection row : Json) :
    row ∈ electionRows subject article projection ↔
      row ∈ eventArray projection "event_candidates" ∧
        electionRowMatches subject article row = true := by
  simp only [electionRows, List.mem_filter]

/-- The query reads the exact original article/SLR projection pair.
    Absence, multiple matching rows, or unmatched lead returns unresolved. -/
abbrev ElectionSource := String × Json

def electionAnswer (source : ElectionSource) (subject : BushOfficeSubject) :
    Option ElectionClaim :=
  if indexedOfficeLeadMatches subject source.1 then
    match electionRows subject source.1 source.2 with
    | [_] => some election2000
    | _ => none
  else none

def electionModel : DocumentQueryModel ElectionSource ElectionSource ElectionSource
    BushOfficeSubject (Option ElectionClaim) where
  observe := id
  live := fun o r => r = o
  documentAnswer := electionAnswer
  readingAnswer := electionAnswer

def electionLicence (source : ElectionSource) (subject : BushOfficeSubject) :
    SourceQueryLicence electionModel source subject where
  observation := source
  sameProducedObservation := rfl
  chosenReading := source
  chosenIsLive := rfl
  consumerFactorises := by
    intro s h
    exact congrArg (fun x => electionAnswer x subject) h
  consumerClosed := by
    intro r h
    exact congrArg (fun x => electionAnswer x subject) h

theorem reciprocalElectionClaimSound
    (a b : ElectionSource)
    (ha : electionAnswer a .son = some election2000)
    (hb : electionAnswer b .father = some election2000) :
    electionModel.documentAnswer a .son = some election2000 ∧
    electionModel.documentAnswer b .father = some election2000 := by
  exact ⟨slrJmdDocumentQuerySound (electionLicence a .son) _ ha,
    slrJmdDocumentQuerySound (electionLicence b .father) _ hb⟩

/-- Compare both directions on the existing two-source licence theorem.
    A proof of shared outcome does not identify the complete source event
    inventories, electoral-vote details or subsequent legal issues. -/
theorem reciprocalElectionReadingsSound (a b : ElectionSource) :
    (decide (electionModel.readingAnswer a .son = electionModel.readingAnswer b .father),
      decide (electionModel.readingAnswer b .father = electionModel.readingAnswer a .son)) =
    (decide (electionModel.documentAnswer a .son = electionModel.documentAnswer b .father),
      decide (electionModel.documentAnswer b .father = electionModel.documentAnswer a .son)) :=
  reciprocalLicensedComparison (electionLicence a .son) (electionLicence b .father)
    (fun x y => decide (x = y)) (fun x y => decide (x = y)) a b rfl rfl


end GwbArticleSystem
end Slr
end Wikidata
