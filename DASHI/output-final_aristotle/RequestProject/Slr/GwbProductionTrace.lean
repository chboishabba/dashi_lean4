import RequestProject.Slr.GwbCanonicalSourceProof
import RequestProject.Slr.DbSourceProducer

/-! C3: original SLR M12/S28 trace on the same pinned article.
No semantic admission is inferred from provenance. -/
namespace Wikidata.Slr.GwbProductionTrace
open Lean
open GwbCanonicalSource

def literalAt (article : String) (m : DbM12Observation) : String :=
  String.ofList ((article.toList.drop m.startChar).take (m.endChar - m.startChar))

def matchingSources (m : DbM12Observation) (s28 : Json) : List Json :=
  (rows s28 "source_statements").filter fun r =>
    field r "statement_ref" == m.statementRef &&
    field r "document_ref" == m.documentRef &&
    field r "source_revision_ref" == m.sourceRevisionRef &&
    field r "exact_span_ref" == m.regionRef

def matchingLinks (m : DbM12Observation) (s28 : Json) : List Json :=
  (rows s28 "statement_observation_links").filter fun r =>
    field r "statement_ref" == m.statementRef &&
    field r "source_revision_ref" == m.sourceRevisionRef &&
    field r "exact_span_ref" == m.regionRef &&
    field r "parser_receipt_ref" == m.parserReceiptRef

def joined (article : String) (slr : Json) (m : DbM12Observation)
    (s28 : Json) (eventRef : String) : Bool :=
  decide (m.startChar < m.endChar ∧ m.endChar ≤ article.toList.length) &&
  (field slr "revision_ref" == m.sourceRevisionRef) &&
  (field ((slr.getObjVal? "parser_receipt").toOption.getD Json.null)
    "document_ref" == m.documentRef) &&
  checkNativeM12Literal (literalAt article m) m &&
  checkS28Provenance s28 eventRef &&
  !(matchingSources m s28).isEmpty &&
  !(matchingLinks m s28).isEmpty

structure CheckedTrace (article : String) (slr projection : Json)
    (m : DbM12Observation) (s28 : Json) (eventRef : String) where
  source : ArticleProof.CheckedArticleExtraction article slr projection
  sameTrace : joined article slr m s28 eventRef = true

theorem checkedTraceSound {article : String} {slr projection : Json}
    {m : DbM12Observation} {s28 : Json} {eventRef : String}
    (t : CheckedTrace article slr projection m s28 eventRef) :
    ArticleProof.checkProjection article slr projection = true ∧
    joined article slr m s28 eventRef = true :=
  ⟨t.source.checked, t.sameTrace⟩

/-- Return only temporal records explicitly citing a matching statement
    AND a matching observation. Not a historical date theorem. -/
def temporalQuery (m : DbM12Observation) (s28 : Json) : List Json :=
  (rows s28 "temporal_assertions").filter fun r =>
    ((r.getObjValAs? (Array String) "statement_refs").toOption.getD #[]).contains m.statementRef &&
    (matchingLinks m s28).any (fun link =>
      ((r.getObjValAs? (Array String) "observation_refs").toOption.getD #[]).contains
        (field link "observation_ref"))

theorem temporalQueryOriginal (m : DbM12Observation) (s28 row : Json)
    (h : row ∈ temporalQuery m s28) :
    row ∈ rows s28 "temporal_assertions" :=
  (List.mem_filter.mp h).1

private def readJson (path : String) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok j => return j
  | .error e => throw (IO.userError e)

def run (articlePath slrPath projectionPath executable parserRun statementRef
    documentRef revision region literalPath eventRef outputPath : String)
    (startChar endChar : Nat) : IO UInt32 := do
  let ok ← ArticleProof.verifyFiles articlePath slrPath projectionPath
  if !ok then return 1
  let article ← IO.FS.readFile articlePath
  let slr ← readJson slrPath
  let projection ← readJson projectionPath
  let m ← callSlrDbM12 executable parserRun statementRef documentRef revision
    region literalPath startChar endChar
  let s28 ← callSlrS28Candidates executable eventRef
  if (← IO.FS.readFile literalPath) != literalAt article m then
    throw (IO.userError "M12 literal differs from pinned article")
  if h : ArticleProof.checkProjection article slr projection = true then
    if j : joined article slr m s28 eventRef = true then
      let t : CheckedTrace article slr projection m s28 eventRef := ⟨⟨h⟩, j⟩
      let _ := checkedTraceSound t
      IO.FS.writeFile outputPath ((Json.mkObj [
        ("schema", toJson ("gwb-native-trace-lean-v1" : String)),
        ("statement_ref", toJson m.statementRef),
        ("document_ref", toJson m.documentRef),
        ("source_revision_ref", toJson m.sourceRevisionRef),
        ("region_ref", toJson m.regionRef),
        ("parser_receipt_ref", toJson m.parserReceiptRef),
        ("literal_sha256", toJson m.sourceLiteralDigest),
        ("event_ref", toJson eventRef),
        ("source_rows", toJson (matchingSources m s28)),
        ("statement_observation_links", toJson (matchingLinks m s28)),
        ("original_s28", s28),
        ("temporal_query", toJson (temporalQuery m s28)),
        ("semantic_identity_paid", toJson false),
        ("event_occurrence_paid", toJson false)]).pretty ++ "\n")
      IO.println "GWB_NATIVE_SAME_SOURCE_TRACE_OK"
      return 0
    else throw (IO.userError "M12/S28 same-source trace mismatch")
  else throw (IO.userError "Original projection rejected")

end Wikidata.Slr.GwbProductionTrace
