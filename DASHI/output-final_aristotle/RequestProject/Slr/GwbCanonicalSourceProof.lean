import RequestProject.Slr.WikipediaArticleProof
import RequestProject.Slr.DocumentQuerySound

/-! Canonical source proof population. SLR is production; Lean/Agda golden.
No experimental semantic-expansion input. These are source observations,
not admitted identities or historical occurrences. -/
namespace Wikidata.Slr.GwbCanonicalSource
open Lean

def rows (j : Json) (key : String) : List Json :=
  ((j.getObjValAs? (Array Json) key).toOption.getD #[]).toList

def field (j : Json) (key : String) : String :=
  (j.getObjValAs? String key).toOption.getD ""

def events (projection : Json) : List Json := rows projection "event_candidates"

structure SourceAnchor (article : String) (slr projection : Json) where
  checked : ArticleProof.CheckedArticleExtraction article slr projection
  event : Json
  present : event ∈ events projection

theorem anchorRetainsOriginal {article : String} {slr projection : Json}
    (a : SourceAnchor article slr projection) :
    ArticleProof.checkProjection article slr projection = true ∧
    a.event ∈ events projection :=
  ⟨a.checked.checked, a.present⟩

/-- Instantiate a proof for every original event, retaining the complete JSON
    rather than collapsing subject/object spans into an alternative vocabulary. -/
def populate {article : String} {slr projection : Json}
    (checked : ArticleProof.CheckedArticleExtraction article slr projection) :
    List (SourceAnchor article slr projection) :=
  (events projection).attach.map fun e => ⟨checked, e.val, e.property⟩

def predicateSurface (event : Json) : String :=
  field ((event.getObjVal? "predicate").toOption.getD Json.null) "surface"

def predicateQuery (projection : Json) (surface : String) : List Json :=
  (events projection).filter (fun e => predicateSurface e == surface)

/-- Concrete source-only query, not a semantic identity answer. -/
theorem predicateQuerySound (projection : Json) (surface : String) (e : Json)
    (h : e ∈ predicateQuery projection surface) :
    e ∈ events projection ∧ predicateSurface e = surface := by
  have hh := List.mem_filter.mp h
  exact ⟨hh.1, beq_iff_eq.mp hh.2⟩

/-- Exact source-observation consumer. The observation is the complete
    original checked event array, not a semantic interpretation. -/
def sourceModel : DocumentQueryModel Json Json Json String (List Json) where
  observe := id
  live := fun observation reading => reading = observation
  documentAnswer := predicateQuery
  readingAnswer := predicateQuery

/-- Source-only predicate query licence: the observation is the original
    projection itself. No semantic completeness or reviewed identity follows. -/
def sourcePredicateLicence (projection : Json) (surface : String) :
    SourceQueryLicence sourceModel projection surface where
  observation := projection
  sameProducedObservation := rfl
  chosenReading := projection
  chosenIsLive := rfl
  consumerFactorises := by
    intro other h
    exact congrArg (fun j => predicateQuery j surface) h
  consumerClosed := by
    intro reading h
    exact congrArg (fun j => predicateQuery j surface) h

theorem licensedPredicateQuerySound (projection : Json) (surface : String) :
    sourceModel.documentAnswer projection surface = predicateQuery projection surface :=
  slrJmdDocumentQuerySound (sourcePredicateLicence projection surface)
    (predicateQuery projection surface) rfl

/-- A source-bound evaluated query with both directions of membership.
    No arbitrary evidence proposition or external identity premise. -/
theorem predicateQueryComplete (projection : Json) (surface : String) (e : Json) :
    e ∈ predicateQuery projection surface ↔
      e ∈ events projection ∧ predicateSurface e = surface := by
  constructor
  · exact predicateQuerySound projection surface e
  · intro h
    exact List.mem_filter.mpr ⟨h.1, beq_iff_eq.mpr h.2⟩

/-- A bounded reporting-clause consumer over the original SLR graph.
    It retains the reporting predicate, complement, coordinated content,
    syntactic participants and independently scoped observed negation.
    The rule is deliberately limited to direct ccomp and one conj edge.
    It does not identify pronouns, infer missing signs, or assert occurrence. -/
abbrev ReportingSource := String × Json × Json

private def natField (j : Json) (k : String) : Option Nat :=
  (j.getObjValAs? Nat k).toOption

private def pred (e : Json) : Json :=
  (e.getObjVal? "predicate").toOption.getD Json.null

private def sameSentence (a b : Json) : Bool :=
  (natField a "sentence_index").isSome &&
  natField a "sentence_index" == natField b "sentence_index" &&
  !(field a "slr_claim_candidate_id").isEmpty &&
  field a "slr_claim_candidate_id" == field b "slr_claim_candidate_id"

private def attached (parent child : Json) (dep : String) : Bool :=
  sameSentence parent child &&
  (natField (pred parent) "i").isSome &&
  natField (pred child) "head_i" == natField (pred parent) "i" &&
  natField (pred child) "i" != natField (pred parent) "i" &&
  field (pred child) "dep" == dep

private def observedNegation (source : ReportingSource) (event : Json) : List Json :=
  (rows source.2.1 "pnf_candidates").flatMap fun sentence =>
    if natField sentence "sentence_index" == natField event "sentence_index" &&
       field sentence "claim_candidate_id" == field event "slr_claim_candidate_id" then
      (rows sentence "dependency_rows").filter fun token =>
        field token "dep" == "neg" &&
        (natField (pred event) "i").isSome &&
        natField token "head_i" == natField (pred event) "i" &&
        (match natField token "idx" with
         | none => false
         | some start =>
           let surface := field token "text"
           !surface.isEmpty &&
           decide (start + surface.toList.length ≤ source.1.toList.length) &&
           String.ofList ((source.1.toList.drop start).take surface.toList.length) == surface)
    else []

private def reportingRow (source : ReportingSource)
    (report complement content : Json) (attachment : String) : Json :=
  Json.mkObj [
    ("report", report), ("complement", complement), ("content", content),
    ("attachment", toJson attachment),
    ("report_negation_tokens", toJson (observedNegation source report)),
    ("complement_negation_tokens", toJson (observedNegation source complement)),
    ("content_negation_tokens", toJson (observedNegation source content))]

def reportingQuery (source : ReportingSource) (lemma : String) : List Json :=
  let es := events source.2.2
  (es.filter (fun e => field (pred e) "lemma" == lemma)).flatMap fun report =>
    (es.filter (fun e => attached report e "ccomp")).flatMap fun complement =>
      reportingRow source report complement complement "ccomp" ::
      ((es.filter (fun e => attached complement e "conj")).map fun content =>
        reportingRow source report complement content "ccomp/conj")

/-- Every semantic completion, represented or not, may vary freely in
    the interpretation coordinate. Only this bounded source-relative
    reporting relation is licensed, not the truth of its reported content. -/
structure ReportingReading where
  original : ReportingSource
  interpretation : Json

def reportingModel : DocumentQueryModel
    ReportingSource ReportingSource ReportingReading String (List Json) where
  observe := id
  live := fun o r => r.original = o
  documentAnswer := reportingQuery
  readingAnswer := fun r => reportingQuery r.original

def reportingLicence (source : ReportingSource) (lemma : String) :
    SourceQueryLicence reportingModel source lemma where
  observation := source
  sameProducedObservation := rfl
  chosenReading := ⟨source, Json.null⟩
  chosenIsLive := rfl
  consumerFactorises := by
    intro other h
    exact congrArg (fun s => reportingQuery s lemma) h
  consumerClosed := by
    intro reading h
    exact congrArg (fun s => reportingQuery s lemma) h

theorem reportingReadingInvariant (source : ReportingSource) (lemma : String)
    (left right : ReportingReading)
    (hl : reportingModel.live source left)
    (hr : reportingModel.live source right) :
    reportingModel.readingAnswer left lemma = reportingModel.readingAnswer right lemma := by
  exact ((reportingLicence source lemma).consumerClosed left hl).trans
    ((reportingLicence source lemma).consumerClosed right hr).symm

theorem checkedReportingAnswerSound
    {article : String} {slr projection : Json}
    (checked : ArticleProof.CheckedArticleExtraction article slr projection)
    (lemma : String) :
    ArticleProof.checkProjection article slr projection = true ∧
      reportingModel.documentAnswer (article, slr, projection) lemma =
        reportingQuery (article, slr, projection) lemma :=
  ⟨checked.checked, slrJmdDocumentQuerySound
    (reportingLicence (article, slr, projection) lemma)
    (reportingQuery (article, slr, projection) lemma) rfl⟩

def run (articlePath sourcePath projectionPath outputPath : String) : IO UInt32 := do
  let ok ← ArticleProof.verifyFiles articlePath sourcePath projectionPath
  if !ok then return 1
  let article ← IO.FS.readFile articlePath
  match Json.parse (← IO.FS.readFile sourcePath), Json.parse (← IO.FS.readFile projectionPath) with
  | .ok slr, .ok projection =>
    if h : ArticleProof.checkProjection article slr projection = true then
      let checked : ArticleProof.CheckedArticleExtraction article slr projection := ⟨h⟩
      let anchors := populate checked
      let output := anchors.map fun a =>
        let _ := anchorRetainsOriginal a
        Json.mkObj [("event", a.event), ("predicate_surface", toJson (predicateSurface a.event))]
      let surfaces := (events projection).map predicateSurface
      let queries := surfaces.eraseDups.map fun surface =>
        let answer := predicateQuery projection surface
        let _ := licensedPredicateQuerySound projection surface
        Json.mkObj [("query", toJson surface), ("answer", toJson answer),
          ("scope", toJson ("original-predicate-surface-only" : String))]
      let reportingSource : ReportingSource := (article, slr, projection)
      let reportQueries := (["state", "claim", "say", "assert", "deny", "report"] : List String).map fun lemma =>
        let _ := checkedReportingAnswerSound checked lemma
        Json.mkObj [("lemma", toJson lemma),
          ("rows", toJson (reportingQuery reportingSource lemma)),
          ("scope", toJson ("original-source-reporting-dependency-v1" : String)),
          ("semantic_identity_paid", toJson false), ("world_truth_paid", toJson false)]
      IO.FS.writeFile outputPath ((Json.mkObj [
        ("schema", toJson ("gwb-canonical-lean-source-instances-v1" : String)),
        ("source_revision", toJson (field slr "revision_ref")),
        ("source_unit_ref", toJson (field slr "source_unit_ref")),
        ("instances", toJson output), ("predicate_queries", toJson queries),
        ("reporting_queries", toJson reportQueries)]).pretty ++ "\n")
      IO.println s!"GWB_CANONICAL_LEAN_INSTANCES count={anchors.length}"
      return 0
    else return 1
  | _, _ => return 1

end Wikidata.Slr.GwbCanonicalSource
