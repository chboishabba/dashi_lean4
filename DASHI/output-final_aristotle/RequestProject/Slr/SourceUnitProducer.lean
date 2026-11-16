/-!
# Direct SLR source-unit PNF producer

Calls the pre-existing DASHI/SLR slr_source_unit_pnf_batch.py script,
which calls the trained spaCy pipeline for arbitrary input text or text_path
from source-unit JSONL. This is a source OBSERVATION interface, not a new
semantic interpreter, licence checker, or evidence admission mechanism.

Inputs are explicit existing paths; the source-unit JSONL must include
source_unit_ref and revision_ref and may include literal text.
The script produces a manifest and separately stored sentence PNF records.

This module consumes the script's actual output; it never invents the words,
source revision, candidate entity, or claimed proof.
-/
import Lean

namespace Wikidata
namespace Slr

open Lean

structure SourceUnitCandidateOutput where
  sourceUnitReference : String
  revisionReference : String
  sourceTextDigest : String
  record : Json
  deriving Repr

/-- Validate a source-unit candidate record before exposing it to Lean
    consumers. Candidate-only output cannot pay semantic admission. -/
def decodeSourceUnitCandidate (record : Json) :
    Option SourceUnitCandidateOutput := do
  let schema ← (record.getObjValAs? String "schema").toOption
  if schema != "slr-source-unit-pnf-record-v1" then none else
    let sourceUnitReference ←
      (record.getObjValAs? String "source_unit_ref").toOption
    let revisionReference ←
      (record.getObjValAs? String "revision_ref").toOption
    let candidateOnly ←
      (record.getObjValAs? Bool "candidate_only").toOption
    let semanticPromotion ←
      (record.getObjValAs? Bool "semantic_promotion").toOption
    let parserTruth ←
      (record.getObjValAs? Bool "parser_output_creates_ontology_truth").toOption
    let roleTruth ←
      (record.getObjValAs? Bool "source_role_creates_claim_truth").toOption
    let manifestation ←
      (record.getObjVal? "manifestation").toOption
    let digest ←
      (manifestation.getObjValAs? String "source_text_sha256").toOption
    let parserReceipt ← (record.getObjVal? "parser_receipt").toOption
    let depParser ←
      (parserReceipt.getObjValAs? Bool "dependency_capable").toOption
    let candidates ←
      (record.getObjValAs? (Array Json) "pnf_candidates").toOption
    if sourceUnitReference.isEmpty || revisionReference.isEmpty ||
        digest.isEmpty || !candidateOnly || semanticPromotion ||
        parserTruth || roleTruth || !depParser || candidates.isEmpty then
      none
    else
      some ⟨sourceUnitReference, revisionReference, digest, record⟩

/-- Call SLR's EXISTING general text producer. No shell is involved.
    All paths and the Python executable are controlled by the invoker.
    Any failed producer, malformed JSON, or promoted output fails closed. -/
def callSlrSourceUnitProducer
    (pythonExecutable scriptPath inputJsonl outputDir manifestPath summaryPath : String) :
    IO (Array SourceUnitCandidateOutput) := do
  let out ← IO.Process.output {
    cmd := pythonExecutable
    args := #[
      scriptPath,
      "--input-jsonl", inputJsonl,
      "--output-dir", outputDir,
      "--manifest", manifestPath,
      "--summary", summaryPath
    ]
  }
  if out.exitCode != 0 then
    throw (IO.userError s!"SLR source-unit producer failed: {out.stderr}")
  let manifest ← IO.FS.readFile manifestPath
  let mut records : Array SourceUnitCandidateOutput := #[]
  for line in manifest.splitOn "\n" do
    if !line.trimAscii.toString.isEmpty then
      let entry ← match Json.parse line with
        | .ok value => pure value
        | .error err =>
            throw (IO.userError s!"Invalid SLR manifest JSON: {err}")
      let recordPath ← match entry.getObjValAs? String "record_path" with
        | .ok path => pure path
        | .error err =>
            throw (IO.userError s!"Missing SLR record path: {err}")
      let body ← IO.FS.readFile recordPath
      let value ← match Json.parse body with
        | .ok v => pure v
        | .error err =>
            throw (IO.userError s!"Invalid SLR candidate record: {err}")
      let candidate ← match decodeSourceUnitCandidate value with
        | some v => pure v
        | none =>
            throw (IO.userError "SLR record is malformed, empty, or semantically promoted")
      let manifestSource ← match entry.getObjValAs? String "source_unit_ref" with
        | .ok v => pure v
        | .error err => throw (IO.userError s!"Missing manifest source: {err}")
      let manifestRev ← match entry.getObjValAs? String "revision_ref" with
        | .ok v => pure v
        | .error err => throw (IO.userError s!"Missing manifest revision: {err}")
      let manifestDigest ← match entry.getObjValAs? String "source_text_sha256" with
        | .ok v => pure v
        | .error err => throw (IO.userError s!"Missing manifest digest: {err}")
      if candidate.sourceUnitReference != manifestSource ||
          candidate.revisionReference != manifestRev ||
          candidate.sourceTextDigest != manifestDigest then
        throw (IO.userError "SLR manifest/record source coordinates disagree")
      records := records.push candidate
  return records

end Slr
end Wikidata
