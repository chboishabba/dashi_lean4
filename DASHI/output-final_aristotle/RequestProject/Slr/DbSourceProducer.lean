/-!
Direct SLR DB M12 source-observation bridge.

The SLR Rust pnf-db-checked command executes its existing
compile_db_statement_pnf_checked against the original PostgreSQL parser run.
This Lean caller checks returned source, parser and region coordinates.
It does NOT prove event occurrence, resolve semantics, or accept a
semantic-licence Boolean. Use SourceQueryLicence for semantic obligations.
-/
import Lean

namespace Wikidata
namespace Slr

open Lean

structure DbM12Observation where
  statementRef : String
  documentRef : String
  sourceRevisionRef : String
  parserRunRef : String
  regionRef : String
  parserReceiptRef : String
  compilationKey : String
  sourceLiteralDigest : String
  startChar : Nat
  endChar : Nat
  candidates : Array Json
  tokens : Array Json
  entities : Array Json
  deriving Repr

private def field? (j : Json) (name : String) : Option String :=
  (j.getObjValAs? String name).toOption

private def bool? (j : Json) (name : String) : Option Bool :=
  (j.getObjValAs? Bool name).toOption

private def nat? (j : Json) (name : String) : Option Nat :=
  (j.getObjValAs? Nat name).toOption

/-- Structural decoder for the DB-native checked M12 product.
    Missing source-join/coverage receipts and promoted status fail closed. -/
def decodeDbM12Observation (j : Json) : Option DbM12Observation := do
  let schema ← field? j "schema"
  if schema != "slr-db-m12-pnf-evidence-v1" then
    none
  else do
    let statementRef ← field? j "statement_ref"
    let documentRef ← field? j "document_ref"
    let sourceRevisionRef ← field? j "source_revision_ref"
    let parserRunRef ← field? j "parser_run_ref"
    let regionRef ← field? j "region_ref"
    let parserReceiptRef ← field? j "parser_receipt_ref"
    let compilationKey ← field? j "compilation_key"
    let sourceLiteralDigest ← field? j "literal_sha256"
    let startChar ← nat? j "start_char"
    let endChar ← nat? j "end_char"
    let sameLiteral ← bool? j "source_literal_and_parser_product_checked"
    let headsCovered ← bool? j "token_head_entity_coverage_checked"
    let revisionJoined ← bool? j "parser_run_source_revision_join_checked"
    let candidateOnly ← bool? j "candidate_only"
    let semanticPaid ← bool? j "semantic_admission_paid"
    let occurrencePaid ← bool? j "world_event_occurrence_paid"
    let truthPaid ← bool? j "claim_truth_paid"
    let candidates ← (j.getObjValAs? (Array Json) "candidates").toOption
    let tokens ← (j.getObjValAs? (Array Json) "tokens").toOption
    let entities ← (j.getObjValAs? (Array Json) "entities").toOption
    if statementRef.isEmpty || documentRef.isEmpty ||
        sourceRevisionRef.isEmpty || parserRunRef.isEmpty ||
        regionRef.isEmpty || parserReceiptRef.isEmpty ||
        compilationKey.isEmpty || sourceLiteralDigest.isEmpty ||
        decide (startChar >= endChar) ||
        !sameLiteral || !headsCovered || !revisionJoined ||
        !candidateOnly || semanticPaid || occurrencePaid || truthPaid ||
        tokens.isEmpty then
      none
    else
      some ⟨statementRef, documentRef, sourceRevisionRef,
        parserRunRef, regionRef, parserReceiptRef, compilationKey,
        sourceLiteralDigest, startChar, endChar, candidates,
        tokens, entities⟩

/-- Directly calls SLR's checked M12 compiler, never the TSV adapter.
    The literal file is checked against parser-product identity and
    token-head-entity source coverage by the existing SLR compiler. -/
def callSlrDbM12
    (slrExecutable parserRun statementRef documentRef sourceRevision
      regionRef literalPath : String)
    (startChar endChar : Nat) : IO DbM12Observation := do
  let result ← IO.Process.output {
    cmd := slrExecutable
    args := #[
      "pnf-db-checked", parserRun, statementRef, documentRef,
      sourceRevision, regionRef, toString startChar, toString endChar,
      literalPath
    ]
  }
  if result.exitCode != 0 then
    throw (IO.userError s!"SLR DB M12 rejected source/parser evidence: {result.stderr}")
  let j ← match Json.parse result.stdout with
    | .ok value => pure value
    | .error err => throw (IO.userError s!"Invalid SLR DB M12 JSON: {err}")
  let observation ← match decodeDbM12Observation j with
    | some value => pure value
    | none => throw (IO.userError "Malformed or promoted SLR DB M12 observation")
  if observation.parserRunRef != parserRun ||
      observation.statementRef != statementRef ||
      observation.documentRef != documentRef ||
      observation.sourceRevisionRef != sourceRevision ||
      observation.regionRef != regionRef ||
      observation.startChar != startChar ||
      observation.endChar != endChar ||
      observation.parserReceiptRef != s!"db-parser:{parserRun}:{regionRef}" then
    throw (IO.userError "SLR DB M12 response mismatches requested source/run/region")
  return observation


/-- Read existing S28 temporal, claim and contestation observations for a
    previously assembled event. This is NOT an automatic event join nor
    a derived world timeline. Its rows remain separately attributable. -/
def callSlrS28Candidates (slrExecutable eventRef : String) : IO Json := do
  if eventRef.isEmpty then
    throw (IO.userError "Event identity is required")
  let result ← IO.Process.output {
    cmd := slrExecutable
    args := #["timeline-candidates", eventRef]
  }
  if result.exitCode != 0 then
    throw (IO.userError s!"SLR S28 retrieval failed: {result.stderr}")
  let value ← match Json.parse result.stdout with
    | .ok j => pure j
    | .error err => throw (IO.userError s!"Invalid S28 JSON: {err}")
  let schema := (value.getObjValAs? String "schema").toOption
  let receivedEvent := (value.getObjValAs? String "event_ref").toOption
  let candidatesOnly := (value.getObjValAs? Bool "candidate_only").toOption
  let promotion := (value.getObjValAs? Bool "semantic_promotion").toOption
  let occurrence := (value.getObjValAs? Bool "event_occurrence_paid").toOption
  let worldTruth := (value.getObjValAs? Bool "source_or_review_receipts_are_world_truth").toOption
  if schema != some "slr-s28-event-chronology-candidates-v1" ||
      receivedEvent != some eventRef || candidatesOnly != some true ||
      promotion != some false || occurrence != some false ||
      worldTruth != some false then
    throw (IO.userError "S28 returned wrong event identity or promoted authority")
  let temporal ← match value.getObjValAs? (Array Json) "temporal_assertions" with
    | .ok a => pure a
    | .error err => throw (IO.userError s!"Missing temporal records: {err}")
  let claims ← match value.getObjValAs? (Array Json) "claim_leaves" with
    | .ok a => pure a
    | .error err => throw (IO.userError s!"Missing claim records: {err}")
  let contestations ← match value.getObjValAs? (Array Json) "contestation_relations" with
    | .ok a => pure a
    | .error err => throw (IO.userError s!"Missing contestation records: {err}")
  if temporal.isEmpty && claims.isEmpty then
    throw (IO.userError "S28 event has no candidate history")
  for row in temporal ++ claims ++ contestations do
    if (row.getObjValAs? Bool "candidate_only").toOption != some true ||
        (row.getObjValAs? Bool "claim_truth_promoted").toOption != some false then
      throw (IO.userError "S28 row attempts to promote claim truth")
  return value

end Slr
end Wikidata
