import Lean

/-!
Direct SLR DB M12 source-observation bridge.

The SLR Rust pnf-db-checked command executes its existing
compile_db_statement_pnf_checked against the original PostgreSQL parser run.
This Lean caller checks returned source, parser and region coordinates.
It does NOT prove event occurrence, resolve semantics, or accept a
semantic-licence Boolean. Use SourceQueryLicence for semantic obligations.
-/

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
    let candidateSpansValid := candidates.all (fun candidate =>
      (candidate.getObjValAs? Bool "candidate_only").toOption == some true &&
      (match (candidate.getObjValAs? Nat "start_char").toOption,
             (candidate.getObjValAs? Nat "end_char").toOption with
       | some a, some b => decide (startChar <= a ∧ a < b ∧ b <= endChar)
       | _, _ => false))
    if statementRef.isEmpty || documentRef.isEmpty ||
        sourceRevisionRef.isEmpty || parserRunRef.isEmpty ||
        regionRef.isEmpty || parserReceiptRef.isEmpty ||
        compilationKey.isEmpty || sourceLiteralDigest.isEmpty ||
        decide (startChar >= endChar) ||
        !sameLiteral || !headsCovered || !revisionJoined ||
        !candidateOnly || semanticPaid || occurrencePaid || truthPaid ||
        tokens.isEmpty || !candidateSpansValid then
      none
    else
      some ⟨statementRef, documentRef, sourceRevisionRef,
        parserRunRef, regionRef, parserReceiptRef, compilationKey,
        sourceLiteralDigest, startChar, endChar, candidates,
        tokens, entities⟩

/-- Independent Lean-side check of the same original literal characters
    and parser-ordinal parent graph returned by the Rust DB M12 compiler.
    Offsets are source-revision absolute; literal text is region-local. -/
private def exactLiteralSpan (literal : String) (spanStart spanEnd : Nat)
    (row : Json) : Bool :=
  match nat? row "start_char", nat? row "end_char", field? row "surface" with
  | some a, some b, some surface =>
      decide (spanStart <= a ∧ a < b ∧ b <= spanEnd) &&
      String.ofList ((literal.toList.drop (a - spanStart)).take (b - a)) ==
        surface
  | _, _, _ => false

private def nativeTokenOrdinal? (token : Json) : Option Nat :=
  nat? token "ordinal"

private def supportedNativeHead
    (tokens : Array Json) (token : Json) : Bool :=
  match nat? token "ordinal", nat? token "head_ordinal" with
  | some _, some head =>
      tokens.toList.any (fun t => nativeTokenOrdinal? t == some head)
  | _, _ => false

private def nativeSourceTokenExact
    (literal : String) (start stop : Nat)
    (tokens : Array Json) (token : Json) : Bool :=
  exactLiteralSpan literal start stop token &&
  supportedNativeHead tokens token &&
  (field? token "lemma").isSome &&
  (field? token "pos").isSome &&
  (field? token "dependency").isSome

private def nativeSourceCandidateExact
    (literal : String) (start stop : Nat)
    (candidate : Json) : Bool :=
  exactLiteralSpan literal start stop candidate &&
  (field? candidate "candidate_ref").isSome &&
  (field? candidate "lemma").isSome &&
  (field? candidate "dependency").isSome &&
  (field? candidate "role").isSome &&
  (["actor", "predicate", "patient", "qualifier", "other"].contains
    ((field? candidate "role").getD "")) &&
  bool? candidate "candidate_only" == some true

private def nativeSourceEntityExact
    (literal : String) (start stop : Nat) (entity : Json) : Bool :=
  exactLiteralSpan literal start stop entity &&
  (nat? entity "ordinal").isSome &&
  (field? entity "label").isSome

/-- A checked M12 response has literal-source witnesses for EVERY token,
    candidate and entity, with complete dependency-head references.
    The proof does not invent named-entity or event-occurrence semantics. -/
def checkNativeM12Literal
    (literal : String) (observation : DbM12Observation) : Bool :=
  let start := observation.startChar
  let stop := observation.endChar
  let tokens := observation.tokens
  let ordinals := tokens.toList.map nativeTokenOrdinal?
  decide (literal.toList.length = stop - start) &&
  decide ordinals.Nodup &&
  tokens.toList.all (nativeSourceTokenExact literal start stop tokens) &&
  observation.candidates.toList.all
    (nativeSourceCandidateExact literal start stop) &&
  observation.entities.toList.all
    (nativeSourceEntityExact literal start stop)

structure CheckedNativeM12Literal
    (literal : String) (observation : DbM12Observation) where
  checked : checkNativeM12Literal literal observation = true

theorem checkedM12AllSourceSpansExact
    {literal : String} {observation : DbM12Observation}
    (receipt : CheckedNativeM12Literal literal observation) :
    checkNativeM12Literal literal observation = true := receipt.checked

/-- Independently reconstruct the bounded reporting projection using the
    original M12 token ordinals. Absence of a sign is not a truth licence. -/
def nativeReportingRows (tokens : Array Json) : Array Json := Id.run do
  let neg := fun head => tokens.filterMap fun t =>
    if nat? t "head_ordinal" == some head && field? t "dependency" == some "neg"
    then nat? t "ordinal" else none
  let mut result := #[]
  for r in tokens do
    if field? r "pos" == some "VERB" &&
        ["state", "claim", "say", "assert", "deny", "report"].contains
          ((field? r "lemma").getD "") then
      if let some ri := nat? r "ordinal" then
        for c in tokens do
          if field? c "pos" == some "VERB" &&
              nat? c "head_ordinal" == some ri &&
              field? c "dependency" == some "ccomp" then
            if let some ci := nat? c "ordinal" then
              let contents := #[(ci, "ccomp")] ++ (tokens.filterMap fun t =>
                if field? t "pos" == some "VERB" &&
                    nat? t "head_ordinal" == some ci &&
                    field? t "dependency" == some "conj" then
                  (nat? t "ordinal").map (fun ti => (ti, "ccomp/conj"))
                else none)
              for (ti, attachment) in contents do
                result := result.push (Json.mkObj [
                  ("report_ordinal", toJson ri),
                  ("complement_ordinal", toJson ci),
                  ("content_ordinal", toJson ti),
                  ("attachment", toJson attachment),
                  ("report_negation_ordinals", toJson (neg ri)),
                  ("complement_negation_ordinals", toJson (neg ci)),
                  ("content_negation_ordinals", toJson (neg ti))])
  return result

def checkNativeReportingRows (j : Json) (observation : DbM12Observation) : Bool :=
  (j.getObjValAs? (Array Json) "reporting_clauses").toOption ==
    some (nativeReportingRows observation.tokens)

theorem checkedNativeReportingRowsExact (j : Json) (observation : DbM12Observation)
    (h : checkNativeReportingRows j observation = true) :
    (j.getObjValAs? (Array Json) "reporting_clauses").toOption ==
      some (nativeReportingRows observation.tokens) = true := h

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
  let literal ← IO.FS.readFile literalPath
  let digestCheck ← IO.Process.output {
    cmd := "sha256sum", args := #[literalPath]
  }
  if digestCheck.exitCode != 0 then
    throw (IO.userError s!"Cannot independently hash M12 literal: {digestCheck.stderr}")
  let literalDigest := (digestCheck.stdout.splitOn " ").head!
  if literalDigest != observation.sourceLiteralDigest then
    throw (IO.userError "Native M12 source hash differs from raw literal UTF-8 SHA-256")
  if h : checkNativeM12Literal literal observation = true then
    let receipt : CheckedNativeM12Literal literal observation := ⟨h⟩
    let _ := checkedM12AllSourceSpansExact receipt
    if hReport : checkNativeReportingRows j observation = true then
      let _ := checkedNativeReportingRowsExact j observation hReport
      return observation
    else
      throw (IO.userError "Native M12 reporting projection missing or mismatched")
  else
    throw (IO.userError "Lean rejected incomplete or forged M12 literal/token/head/role coordinates")


/-- Original S28 source-trace completeness must be reconstructed from
    retained rows; accepting a producer-supplied true Boolean is insufficient.
    This stays strictly at the provenance boundary, before *semantic* review. -/
private def strArray? (j : Json) (key : String) : Option (Array String) :=
  (j.getObjValAs? (Array String) key).toOption

private def noRepeatedRefs (rows : Array Json) (field : String) : Bool :=
  let refs := rows.toList.map (fun r => field? r field)
  refs.all (fun ref => ref.isSome && !((ref.getD "").isEmpty)) &&
    decide refs.Nodup

private def sourceForStatement
    (sources : Array Json) (statement : String) : Option Json :=
  sources.toList.find? (fun row => field? row "statement_ref" == some statement)

private def statementLinkSourceExact
    (sources : Array Json) (link : Json) : Bool :=
  match field? link "statement_ref" with
  | none => false
  | some statement =>
    match sourceForStatement sources statement with
    | none => false
    | some source =>
      field? link "source_revision_ref" ==
        field? source "source_revision_ref" &&
      field? link "exact_span_ref" == field? source "exact_span_ref" &&
      (field? source "source_revision_ref").isSome &&
      (field? source "exact_span_ref").isSome

private def hasSourceBackedLink
    (sources links : Array Json) (observation : String) : Bool :=
  links.toList.any (fun link =>
    field? link "observation_ref" == some observation &&
    statementLinkSourceExact sources link)

private def sourceAndObservationRefsBacked
    (sources assemblies links : Array Json) (row : Json) : Bool :=
  match strArray? row "statement_refs",
        strArray? row "observation_refs" with
  | some statements, some observations =>
      statements.toList.all (fun ref =>
        (sourceForStatement sources ref).isSome) &&
      observations.toList.all (fun ref =>
        assemblies.toList.any (fun assembly =>
          field? assembly "observation_ref" == some ref) &&
        hasSourceBackedLink sources links ref)
  | _, _ => false

/-- These are original SLR adjacency and source-ancestry relations, not
    semantic equivalence, same historical event, or temporal truth. -/
def checkS28Provenance (j : Json) (eventRef : String) : Bool :=
  let sources := (j.getObjValAs? (Array Json) "source_statements").toOption
  let assemblies := (j.getObjValAs? (Array Json) "observation_event_links").toOption
  let links := (j.getObjValAs? (Array Json) "statement_observation_links").toOption
  let times := (j.getObjValAs? (Array Json) "temporal_assertions").toOption
  let claims := (j.getObjValAs? (Array Json) "claim_leaves").toOption
  let disputes := (j.getObjValAs? (Array Json) "contestation_relations").toOption
  match sources, assemblies, links, times, claims, disputes with
  | some sourceRows, some eventLinks, some statementLinks,
    some temporal, some leaves, some contestations =>
      field? j "schema" == some "slr-s28-event-chronology-candidates-v1" &&
      field? j "event_ref" == some eventRef &&
      bool? j "candidate_only" == some true &&
      bool? j "source_or_review_receipts_are_world_truth" == some false &&
      bool? j "event_occurrence_paid" == some false &&
      bool? j "semantic_promotion" == some false &&
      bool? j "source_trace_join_complete" == some true &&
      (!temporal.isEmpty || !leaves.isEmpty) &&
      (sourceRows ++ eventLinks ++ statementLinks ++ temporal ++
        leaves ++ contestations).toList.all (fun row =>
          bool? row "candidate_only" == some true &&
          bool? row "creates_semantic_authority" == some false &&
          bool? row "applicability_promoted" == some false &&
          bool? row "claim_truth_promoted" == some false) &&
      !sourceRows.isEmpty && !eventLinks.isEmpty &&
      !statementLinks.isEmpty && !eventRef.isEmpty &&
      noRepeatedRefs sourceRows "statement_ref" &&
      noRepeatedRefs eventLinks "link_ref" &&
      noRepeatedRefs statementLinks "link_ref" &&
      eventLinks.toList.all (fun assembly =>
        field? assembly "event_ref" == some eventRef &&
        (match field? assembly "observation_ref" with
         | none => false
         | some observation =>
           (temporal ++ leaves ++ contestations).toList.any (fun row =>
             ((strArray? row "observation_refs").getD #[]).contains observation) &&
           hasSourceBackedLink sourceRows statementLinks observation)) &&
      statementLinks.toList.all (fun link =>
        match field? link "observation_ref", field? link "statement_ref" with
        | some observation, some statement =>
            eventLinks.toList.any (fun assembly =>
              field? assembly "observation_ref" == some observation) &&
            (sourceForStatement sourceRows statement).isSome &&
            statementLinkSourceExact sourceRows link
        | _, _ => false) &&
      (temporal ++ leaves ++ contestations).toList.all
        (sourceAndObservationRefsBacked sourceRows eventLinks statementLinks) &&
      leaves.toList.all (fun claim =>
        match strArray? claim "temporal_refs" with
        | none => false
        | some refs => refs.toList.all (fun ref =>
            temporal.toList.any (fun assertion =>
              field? assertion "temporal_ref" == some ref))) &&
      contestations.toList.all (fun relation =>
        leaves.toList.any (fun claim =>
          field? claim "claim_ref" == field? relation "from_claim_ref") &&
        leaves.toList.any (fun claim =>
          field? claim "claim_ref" == field? relation "to_claim_ref"))
  | _, _, _, _, _, _ => false

structure CheckedS28Provenance (j : Json) (eventRef : String) where
  checked : checkS28Provenance j eventRef = true

theorem checkedS28HasCompleteAncestry
    {j : Json} {eventRef : String}
    (receipt : CheckedS28Provenance j eventRef) :
    checkS28Provenance j eventRef = true := receipt.checked

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
  let sourceRows ← match value.getObjValAs? (Array Json) "source_statements" with
    | .ok a => pure a
    | .error err => throw (IO.userError s!"Missing M12 source rows: {err}")
  let assemblyRows ← match value.getObjValAs? (Array Json) "observation_event_links" with
    | .ok a => pure a
    | .error err => throw (IO.userError s!"Missing M12 event assembly: {err}")
  let statementLinks ← match value.getObjValAs? (Array Json) "statement_observation_links" with
    | .ok a => pure a
    | .error err => throw (IO.userError s!"Missing M12 statement links: {err}")
  let traceComplete := (value.getObjValAs? Bool "source_trace_join_complete").toOption
  if traceComplete != some true then
    throw (IO.userError "Unverified or incomplete M12 -> S28 source trace; refusing JMD proof handoff")
  for row in assemblyRows do
    if (row.getObjValAs? String "event_ref").toOption != some eventRef then
      throw (IO.userError "S28 assembly references a different event")
  if proof : checkS28Provenance value eventRef = true then
    let receipt : CheckedS28Provenance value eventRef := ⟨proof⟩
    let _ := checkedS28HasCompleteAncestry receipt
    pure ()
  else
    throw (IO.userError "S28 provenance graph does not commute: missing source/observation/claim edges")
  if temporal.isEmpty && claims.isEmpty then
    throw (IO.userError "S28 event has no candidate history")
  for row in temporal ++ claims ++ contestations ++ sourceRows ++ assemblyRows ++ statementLinks do
    if (row.getObjValAs? Bool "candidate_only").toOption != some true ||
        (row.getObjValAs? Bool "creates_semantic_authority").toOption != some false ||
        (row.getObjValAs? Bool "applicability_promoted").toOption != some false ||
        (row.getObjValAs? Bool "claim_truth_promoted").toOption != some false then
      throw (IO.userError "S28 row attempts to promote claim truth")
  return value

end Slr
end Wikidata
