import RequestProject.Slr.IndexedWorldFibreInspection

open Lean

def genericRootCheck (qid title article : String) (source projection entity : Json) : Bool :=
  let revision := (source.getObjValAs? String "revision_ref").toOption.getD ""
  let sourceUnit := (source.getObjValAs? String "source_unit_ref").toOption.getD ""
  Wikidata.Slr.ArticleProof.checkProjectionFor qid article source projection &&
  Wikidata.Slr.GwbArticleIdentity.checkSitelink qid title entity &&
  Wikidata.Slr.GwbWorldGraph.jsonEntityMatchesQid qid entity &&
  revision.startsWith "source-revision:" &&
  sourceUnit.startsWith "source:wikipedia:" &&
  !sourceUnit.isEmpty

private def readJson (path : String) : IO (Option Json) := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok value => pure (some value)
  | .error err =>
      IO.eprintln s!"invalid JSON {path}: {err}"
      pure none

private def digestFile (path : String) : IO (Option String) := do
  let result ← IO.Process.output { cmd := "sha256sum", args := #[path] }
  if result.exitCode != 0 then return none
  let digest := (result.stdout.splitOn " ").head!
  return if digest.length == 64 then some digest else none

def main (args : List String) : IO UInt32 := do
  match args with
  | [qid, title, articlePath, slrPath, projectionPath, entityPath, outputPath, propertiesFile] =>
      let article ← IO.FS.readFile articlePath
      let some source ← readJson slrPath | return 1
      let some projection ← readJson projectionPath | return 1
      let some entity ← readJson entityPath | return 1
      let some articleDigest ← digestFile articlePath | return 1
      let some sourceDigest ← digestFile slrPath | return 1
      let some projectionDigest ← digestFile projectionPath | return 1
      let some entityDigest ← digestFile entityPath | return 1
      let manifest := (source.getObjVal? "manifestation").toOption.getD Json.null
      if (manifest.getObjValAs? String "source_text_sha256").toOption != some articleDigest ||
         (projection.getObjValAs? String "source_text_sha256").toOption != some articleDigest then
        IO.eprintln "INDEXED_WORLD_FIBRE_REJECTED: source digest mismatch"
        return 1
      let entities := (entity.getObjVal? "entities").toOption.getD Json.null
      let record := (entities.getObjVal? qid).toOption.getD Json.null
      let some entityRevision := (record.getObjValAs? Nat "lastrevid").toOption | return 1
      if entityRevision == 0 then return 1
      let properties := (← IO.FS.readFile propertiesFile).splitOn "\n"
        |>.filter (fun p => !p.isEmpty)
      if h : genericRootCheck
          qid title article source projection entity = true then
        let inventory := Wikidata.Slr.IndexedWorldFibreInspection.inventory
            qid title source projection entity properties
        IO.FS.writeFile outputPath ((Json.mkObj [
          ("schema", toJson ("slr.jmd-indexed-world-fibre-receipt.v1" : String)),
          ("qid", toJson qid), ("title", toJson title),
          ("source_sha256", toJson articleDigest),
          ("original_slr_sha256", toJson sourceDigest),
          ("projection_sha256", toJson projectionDigest),
          ("entity_sha256", toJson entityDigest),
          ("entity_revision", toJson entityRevision),
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
