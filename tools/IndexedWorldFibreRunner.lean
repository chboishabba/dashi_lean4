import RequestProject.Slr.IndexedWorldFibreInspection

open Lean

private def readJson (path : String) : IO (Option Json) := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok value => pure (some value)
  | .error err =>
      IO.eprintln s!"invalid JSON {path}: {err}"
      pure none

def main (args : List String) : IO UInt32 := do
  match args with
  | [qid, title, articlePath, slrPath, projectionPath, entityPath, outputPath, propertiesFile] =>
      let article ← IO.FS.readFile articlePath
      let some source ← readJson slrPath | return 1
      let some projection ← readJson projectionPath | return 1
      let some entity ← readJson entityPath | return 1
      let properties := (← IO.FS.readFile propertiesFile).splitOn "\n"
        |>.filter (fun p => !p.isEmpty)
      if h : Wikidata.Slr.IndexedWorldFibreInspection.checkRoot
          qid title article source projection entity = true then
        let checked : Wikidata.Slr.IndexedWorldFibreInspection.CheckedRoot
            qid title article source projection entity := ⟨h⟩
        let inventory := Wikidata.Slr.IndexedWorldFibreInspection.inventory
            qid title source projection entity properties
        IO.FS.writeFile outputPath ((Json.mkObj [
          ("schema", toJson ("slr.jmd-indexed-world-fibre-receipt.v1" : String)),
          ("qid", toJson qid), ("title", toJson title),
          ("source_observation_checked", toJson true),
          ("inventory", inventory),
          ("cross_source_alignment_paid", toJson false),
          ("world_truth_paid", toJson false)]).pretty ++ "\n")
        IO.println "INDEXED_WORLD_FIBRE_KERNEL_OK"
        return 0
      else
        IO.eprintln "INDEXED_WORLD_FIBRE_REJECTED: source/article/entity checks failed"
        return 1
  | _ =>
      IO.eprintln "usage: lake env lean --run tools/IndexedWorldFibreRunner.lean QID TITLE ARTICLE SLR PROJECTION ENTITY OUTPUT PROPERTIES"
      return 2

#print axioms Wikidata.Slr.IndexedWorldFibreInspection.independentlyCheckedMembers
