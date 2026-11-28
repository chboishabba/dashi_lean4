import RequestProject.Slr.GwbExactEntityOffice
open Lean
open Wikidata.Slr.GwbExactEntityOffice
open Wikidata.Slr.GwbArticleSystemSoundness

def main (args : List String) : IO UInt32 := do
  match args with
  | [path, revision] =>
    let some rev := revision.toNat? | return 2
    let raw ← IO.FS.readFile path
    let .ok entity := Json.parse raw | return 3
    if entityRevision entity "Q207" != some rev then return 3
    let result ← IO.Process.output { cmd := "sha256sum", args := #[path] }
    if result.exitCode != 0 then return 3
    let sha := (result.stdout.splitOn " ").head!
    let rows := exactOfficeRows entity
    IO.println ((Json.mkObj [
      ("schema", toJson ("slr.gwb-golden-entity-office.v1" : String)),
      ("entity_revision",toJson rev),("source_sha256",toJson sha),
      ("matching_statement_count",toJson rows.length),
      ("witness", (exactOfficeWitness entity).getD Json.null),
      ("world_truth_paid",toJson false)]).compress)
    return 0
  | _ => return 2
