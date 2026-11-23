/-!
P10 minimal independent Q207 EntityData check.
Imports JMD's original Cli.Import only; does not evaluate or import the
643-sentence GWB article, native \`he\` binding or world-property graph.
Source identity is snapshot-relative, not a cross-document mention witness.
Original importer attribution: meta-introspector JMD.
-/
import RequestProject.Cli.Import

open Lean

namespace Wikidata.Slr.GwbQ207Minimal

private def q207Entity (json : Json) : Json :=
  let entities := (json.getObjVal? "entities").toOption.getD Json.null
  (entities.getObjVal? "Q207").toOption.getD Json.null

/-- Exact independent ID, en label and enwiki sitelink; no source projection. -/
def check (json : Json) : Bool :=
  let entity := q207Entity json
  (entity.getObjValAs? String "id").toOption == some "Q207" &&
    Wikidata.Cli.entityLabelIn entity "en" == some "George W. Bush" &&
    Wikidata.Cli.entityEnwikiTitle entity == some "George W. Bush"

structure Checked (json : Json) where
  checked : check json = true

theorem checkedSourceFields {json : Json} (h : Checked json) :
    check json = true := h.checked

end Wikidata.Slr.GwbQ207Minimal

/-- Run a *small* checked JMD property, without projecting the full article. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
    let source ← IO.FS.readFile path
    match Json.parse source with
    | .error err =>
      IO.eprintln s!"GWB_Q207_MINIMAL_REJECTED: invalid JSON {err}"
      return 1
    | .ok json =>
      if h : Wikidata.Slr.GwbQ207Minimal.check json = true then
        let witness : Wikidata.Slr.GwbQ207Minimal.Checked json := ⟨h⟩
        let _ := Wikidata.Slr.GwbQ207Minimal.checkedSourceFields witness
        IO.println "GWB_Q207_MINIMAL_KERNEL_OK"
        IO.println "Q207 ID/English label/enwiki sitelink agree in supplied EntityData JSON only"
        IO.println "Not a native he identity, article digest, property, historical truth or shared snapshot proof"
        return 0
      else
        IO.eprintln "GWB_Q207_MINIMAL_REJECTED: QID/English label/enwiki sitelink mismatch"
        return 1
  | _ =>
    IO.eprintln "usage: lake env lean --run tools/GwbQ207MinimalRunner.lean Q207-EntityData.json"
    return 2

#print axioms Wikidata.Slr.GwbQ207Minimal.checkedSourceFields
