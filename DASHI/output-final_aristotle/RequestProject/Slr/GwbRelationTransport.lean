import RequestProject.Slr.GwbCanonicalSourceProof

namespace Wikidata.Slr.GwbRelationTransport
open Lean GwbCanonicalSource

def nat (j : Json) (k : String) : Option Nat := (j.getObjValAs? Nat k).toOption
def kind (dep : String) : Option String :=
  match dep with
  | "prep" => some "preposition"
  | "pobj" => some "prepositional_object"
  | "pcomp" => some "prepositional_complement"
  | "agent" => some "passive_agent_marker"
  | "dative" => some "dative"
  | "case" => some "case_marker"
  | "prt" => some "particle"
  | _ => none

def expected (slr : Json) : List Json :=
  (rows slr "pnf_candidates").flatMap fun s =>
    (rows s "dependency_rows").filterMap fun t => do
      let k ← kind (field t "dep")
      let sid ← nat s "sentence_index"
      let i ← nat t "i"
      let h ← nat t "head_i"
      let a ← nat t "idx"
      some (Json.mkObj [("sentence_index", toJson sid), ("token_i", toJson i),
        ("head_i", toJson h), ("start_char", toJson a),
        ("end_char", toJson (a + (field t "text").toList.length)),
        ("kind", toJson k), ("candidate_only", toJson true),
        ("context_resolution_required", toJson true)])

def check (slr receipt : Json) : Bool :=
  let actual := rows receipt "relations"
  let targets := expected slr
  field receipt "source_revision" == field slr "revision_ref" &&
  field receipt "source_unit_ref" == field slr "source_unit_ref" &&
  actual.length == targets.length &&
  actual.eraseDups.length == actual.length &&
  targets.eraseDups.length == targets.length &&
  actual.all (fun r => targets.contains r) &&
  targets.all (fun r => actual.contains r)

structure Checked (article : String) (slr projection receipt : Json) where
  source : ArticleProof.CheckedArticleExtraction article slr projection
  relationCheck : check slr receipt = true

theorem retainsOriginal {article : String} {slr projection receipt : Json}
    (c : Checked article slr projection receipt) :
    ArticleProof.checkProjection article slr projection = true ∧ check slr receipt = true :=
  ⟨c.source.checked, c.relationCheck⟩

def run (articlePath slrPath projectionPath receiptPath : String) : IO UInt32 := do
  let ok ← ArticleProof.verifyFiles articlePath slrPath projectionPath
  if !ok then return 1
  let article ← IO.FS.readFile articlePath
  match Json.parse (← IO.FS.readFile slrPath), Json.parse (← IO.FS.readFile projectionPath),
      Json.parse (← IO.FS.readFile receiptPath) with
  | .ok slr, .ok projection, .ok receipt =>
    if h : ArticleProof.checkProjection article slr projection = true then
      if r : check slr receipt = true then
        let c : Checked article slr projection receipt := ⟨⟨h⟩, r⟩
        let _ := retainsOriginal c
        IO.println s!"GWB_RELATION_TRANSPORT_OK count={(rows receipt "relations").length}"
        return 0
      else
        IO.eprintln "GWB_RELATION_TRANSPORT_REJECTED"
        return 1
    else return 1
  | _, _, _ => return 1

end Wikidata.Slr.GwbRelationTransport
