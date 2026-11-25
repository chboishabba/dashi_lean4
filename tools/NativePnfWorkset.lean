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

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let raw ← stdin.readToEnd
  match Json.parse raw >>= produceWorkset with
  | .ok output =>
      IO.println output.compress
      return 0
  | .error reason =>
      IO.eprintln reason
      return 1
