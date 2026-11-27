import RequestProject.Slr.NumericPnfRustPortContract

/-! Executable physical workset producer from the existing formal contract.
The exact source/parser manifest and stable sentence refs are supplied by
the original SLR DB owner. This program selects missing required refs;
it cannot produce source observations, semantic refutation or identity.
Rust must independently check the returned workset before writes. -/

open Lean
open Wikidata.Slr.NumericPnfRustPortContract

def produceWorkset (j : Json) : Except String Json := do
  let schema ← j.getObjValAs? String "schema"
  let source ← j.getObjValAs? String "source_sha256"
  let run ← j.getObjValAs? String "numeric_run_ref"
  let required ← j.getObjValAs? (List String) "required_sentence_refs"
  let published ← j.getObjValAs? (List String) "already_published_required_refs"
  if schema != "slr-native-prefix-workset-input-v1" ||
      source.length != 64 || run.isEmpty ||
      required.any (fun s => s.isEmpty) ||
      published.any (fun s => !(required.contains s)) then
    throw "invalid source-bound workset input"
  let missing := consumerRegionWork required published
  return Json.mkObj [
    ("schema", toJson "slr-native-prefix-workset-output-v1"),
    ("source_sha256", toJson source),
    ("numeric_run_ref", toJson run),
    ("required_sentence_refs", toJson required),
    ("already_published_required_refs", toJson published),
    ("missing_required_sentence_refs", toJson missing),
    ("semantic_admission_paid", toJson false),
    ("identity_paid", toJson false)]

/-! Original m086 typed live-fibre specialization. The SQL owner supplies
the exact represented keys and latest admissibility event/evidence. A
preference, signed residual or inactive execution state never removes a
key. This executable produces the represented live fibre, not a coverage
witness, admitted identity, or authenticated kernel receipt. -/
def decodeKey (j : Json) : Except String CandidateKey := do
  let kind ← j.getObjValAs? Nat "target_kind"
  let id ← j.getObjValAs? Nat "target_id"
  if kind == 0 || id == 0 then throw "invalid typed key"
  return ⟨kind, id⟩

def encodeKey (k : CandidateKey) : Json :=
  Json.mkObj [("target_kind", toJson k.kind), ("target_id", toJson k.id)]

-- Emit only numeric Lean literals. Source strings are never interpolated
-- into executable proof syntax. The checker separately binds the full input
-- digest and original same-key evidence payload.
def keyListSource (ks : List CandidateKey) : String :=
  "[" ++ String.intercalate ", " (ks.map fun k =>
    "⟨" ++ toString k.kind ++ ", " ++ toString k.id ++ "⟩") ++ "]"

def typedProjectionProofSource (represented refuted live : List CandidateKey) : String :=
  "import RequestProject.Slr.NumericPnfRustPortContract\n" ++
  "open Wikidata.Slr.NumericPnfRustPortContract\n" ++
  "set_option maxRecDepth 1000000 in\n" ++
  "theorem slrTypedProjectionCertificate : liveTypedKeys " ++
    keyListSource represented ++ " " ++ keyListSource refuted ++
    " = " ++ keyListSource live ++ " := by decide\n" ++
  "#print axioms slrTypedProjectionCertificate\n"

def produceTypedEvidence (j : Json) : Except String Json := do
  let source ← j.getObjValAs? String "source_sha256"
  let revision ← j.getObjValAs? String "source_revision_ref"
  let run ← j.getObjValAs? String "numeric_run_ref"
  let snapshot ← j.getObjValAs? String "snapshot_ref"
  let digest ← j.getObjValAs? String "input_digest"
  let demand ← j.getObjValAs? Nat "demand_id"
  let obj ← j.getObjValAs? Nat "source_object_id"
  let outside ← j.getObjValAs? Bool "outside_model_possible"
  let rows ← j.getObjValAs? (List Json) "candidates"
  if source.length != 64 || digest.length != 64 || revision.isEmpty ||
      run.isEmpty || snapshot.isEmpty || demand == 0 || obj == 0 then
    throw "invalid typed evidence scope"
  let mut represented : List CandidateKey := []
  let mut refuted : List CandidateKey := []
  for row in rows do
    let k ← decodeKey row
    if represented.contains k then throw "duplicate typed candidate"
    represented := represented ++ [k]
    let isRefuted ← row.getObjValAs? Bool "refuted"
    let event ← row.getObjValAs? Nat "event_kind"
    let eid ← row.getObjValAs? Nat "event_id"
    if isRefuted != (event == 1) || event > 2 then
      throw "inconsistent original admissibility event"
    if event != 0 then
      let ed ← row.getObjValAs? Nat "evidence_demand"
      let ek ← row.getObjValAs? Nat "evidence_target_kind"
      let et ← row.getObjValAs? Nat "evidence_target_id"
      let er ← row.getObjValAs? String "evidence_ref"
      let evidenceId ← row.getObjValAs? Nat "evidence_id"
      let evidence : CandidateEvidence := ⟨ed, ⟨ek, et⟩, er⟩
      if eid == 0 || evidenceId == 0 || !checkedRefutation demand k evidence then
        throw "foreign or missing original event evidence"
    else if eid != 0 then
      throw "unexpected event ID"
    if isRefuted then refuted := refuted ++ [k]
  let live := liveTypedKeys represented refuted
  return Json.mkObj [
    ("schema", toJson "slr-native-typed-evidence-output-v1"),
    ("source_sha256", toJson source), ("source_revision_ref", toJson revision),
    ("numeric_run_ref", toJson run), ("snapshot_ref", toJson snapshot),
    ("input_digest", toJson digest), ("demand_id", toJson demand),
    ("source_object_id", toJson obj), ("outside_model_possible", toJson outside),
    ("represented", toJson (represented.map encodeKey)),
    ("refuted", toJson (refuted.map encodeKey)),
    ("live", toJson (live.map encodeKey)),
    ("proof_source", toJson (typedProjectionProofSource represented refuted live)),
    ("typed_coverage_paid", toJson false), ("identity_paid", toJson false)]

def dispatch (j : Json) : Except String Json := do
  let schema ← j.getObjValAs? String "schema"
  if schema == "slr-native-typed-evidence-input-v1" then produceTypedEvidence j
  else produceWorkset j

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let raw ← stdin.readToEnd
  match Json.parse raw >>= dispatch with
  | .ok output =>
      IO.println output.compress
      return 0
  | .error reason =>
      IO.eprintln reason
      return 1
