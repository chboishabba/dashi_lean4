import Lean

/-!
JMD Wikidata -> SLR direct producer extension.
Original JMD Wikidata Lean CLI: meta-introspector, attributed in Cli/Fetch and Cli/Tool.
This DASHI extension calls the *existing* SLR Rust producer by process invocation.
It does not reimplement spaCy, review, semantic resolution, or Wikidata alignment.

The first executable producer is the SLR IndexedSpacyTsvAdapter compatibility
surface. It has no DB-native attestation; never claim that it does. Future
production callers should use the same typed interface with SLR's checked
PostgreSQL source/PNF entry point.
-/

namespace Wikidata
namespace Slr

open Lean

structure Candidate where
  reference : String
  role : String
  startChar : Nat
  endChar : Nat
  surface : String
  lemma : String
  dependency : String
  candidateOnly : Bool
  deriving Repr, Inhabited

structure ProducerOutput where
  producer : String
  spanReference : String
  startChar : Nat
  endChar : Nat
  inputDigest : String
  sourceRevisionVerified : Bool
  parserEvidenceVerified : Bool
  semanticAdmissionPaid : Bool
  propositionSupportPaid : Bool
  applicabilityPaid : Bool
  claimTruthPaid : Bool
  candidates : Array Candidate
  deriving Repr, Inhabited

private def field? (j : Json) (name : String) : Option String :=
  (j.getObjValAs? String name).toOption

private def natField? (j : Json) (name : String) : Option Nat :=
  (j.getObjValAs? Nat name).toOption

private def boolField? (j : Json) (name : String) : Option Bool :=
  (j.getObjValAs? Bool name).toOption

def decodeCandidate (j : Json) : Option Candidate := do
  let reference ← field? j "candidate_ref"
  let role ← field? j "role"
  let startChar ← natField? j "start_char"
  let endChar ← natField? j "end_char"
  let surface ← field? j "surface"
  let lemma ← field? j "lemma"
  let dependency ← field? j "dependency"
  let candidateOnly ← boolField? j "candidate_only"
  if !candidateOnly || reference.isEmpty || decide (startChar >= endChar) then
    none
  else
    some ⟨reference, role, startChar, endChar, surface, lemma, dependency, candidateOnly⟩

/-- Decode the native SLR output, rejecting parser records that attempt to pay
    any semantic, proposition, applicability or truth authority. -/
def decodeProducerOutput (j : Json) : Option ProducerOutput := do
  let version ← field? j "version"
  if version != "slr-pnf-candidate-v1" then
    none
  else do
    let producer ← field? j "producer"
    let spanReference ← field? j "exact_span_ref"
    let startChar ← natField? j "source_start_char"
    let endChar ← natField? j "source_end_char"
    let inputDigest ← field? j "parser_input_sha256"
    let sourceRevisionVerified ← boolField? j "source_revision_verified"
    let parserEvidenceVerified ← boolField? j "parser_evidence_verified"
    let semanticAdmissionPaid ← boolField? j "semantic_admission_paid"
    let propositionSupportPaid ← boolField? j "proposition_support_paid"
    let applicabilityPaid ← boolField? j "applicability_paid"
    let claimTruthPaid ← boolField? j "claim_truth_paid"
    let candidatesJson ← (j.getObjValAs? (Array Json) "candidates").toOption
    let candidates ← candidatesJson.toList.mapM decodeCandidate
    if spanReference.isEmpty || decide (startChar >= endChar) ||
        sourceRevisionVerified || parserEvidenceVerified ||
        semanticAdmissionPaid || propositionSupportPaid ||
        applicabilityPaid || claimTruthPaid ||
        !(candidates.all fun c => decide (startChar <= c.startChar ∧ c.endChar <= endChar)) then
      none
    else
      some ⟨producer, spanReference, startChar, endChar, inputDigest,
        sourceRevisionVerified, parserEvidenceVerified, semanticAdmissionPaid,
        propositionSupportPaid, applicabilityPaid, claimTruthPaid,
        candidates.toArray⟩

/-- Directly invoke the SLR native producer, as the JMD Wikidata CLI invokes
    its external Wikidata getter. The binary path is explicit, not a shell
    interpolation. No proof or review authority is imported from process exit. -/
def querySlrCandidate
    (slrExecutable tsvPath spanReference : String)
    (startChar endChar : Nat) : IO ProducerOutput := do
  let output ← IO.Process.output {
    cmd := slrExecutable
    args := #["pnf-candidate", tsvPath, spanReference,
      toString startChar, toString endChar]
  }
  if output.exitCode != 0 then
    throw (IO.userError s!"SLR producer failed: {output.stderr}")
  let json ← match Json.parse output.stdout with
    | .ok j => pure j
    | .error e => throw (IO.userError s!"Invalid SLR JSON: {e}")
  match decodeProducerOutput json with
  | none => throw (IO.userError "SLR returned malformed or authority-promoted candidate output")
  | some result =>
      if result.spanReference != spanReference ||
          result.startChar != startChar || result.endChar != endChar then
        throw (IO.userError "SLR response does not match requested source span")
      return result

/-- A parser candidate is only a *possible* referent or role. It cannot
    manufacture the reviewed Wikidata item, P31/P279 assertion, or legal fact. -/
def mayEnterCandidateResolution (output : ProducerOutput) : Bool :=
  !output.sourceRevisionVerified && !output.parserEvidenceVerified &&
    !output.semanticAdmissionPaid && !output.propositionSupportPaid &&
    !output.applicabilityPaid && !output.claimTruthPaid

/-- The source-relative producer flags are preserved in their own coordinates;
    no Lean theorem changes a parser observation into an admitted Wikidata fact. -/
theorem candidateResolution_ne_semanticAdmission
    (o : ProducerOutput) (h : mayEnterCandidateResolution o = true) :
    o.semanticAdmissionPaid = false := by
  simp_all [mayEnterCandidateResolution]

end Slr
end Wikidata
