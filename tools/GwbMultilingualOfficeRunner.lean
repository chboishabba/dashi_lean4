import RequestProject.Slr.GwbMultilingualOffice
open Lean
open Wikidata.Slr.GwbMultilingualOffice
open Wikidata.Slr.WorldSemanticFibre

def editionName : Edition → String
  | .en => "en"
  | .simple => "simple"
  | .es => "es"

def supportJson : Option Support → Json
  | none => Json.null
  | some s => Json.mkObj [("positive", toJson s.positive), ("negative", toJson s.negative)]

def checkSource (e : Edition) (path : String) : IO (Option Json) := do
  let article ← IO.FS.readFile path
  let digest ← IO.Process.output { cmd := "sha256sum", args := #[path] }
  if digest.exitCode != 0 then return none
  let sha := (digest.stdout.splitOn " ").head!
  if sha.length != 64 then return none
  let s : Source := (e, article)
  if !article.startsWith (lead e) || !predicateMatches s then return none
  let (a,b,literal) := occurrence e
  return some (Json.mkObj [
    ("edition", toJson (editionName e)),
    ("source_sha256", toJson sha),
    ("predicate_span", toJson [a,b]),
    ("predicate", toJson literal),
    ("year_support", supportJson (attachedAnswer s yearQuery)),
    ("day_support", supportJson (attachedAnswer s dayQuery))])

def main (args : List String) : IO UInt32 := do
  match args with
  | [enPath, simplePath, esPath] =>
    let some en ← checkSource .en enPath | return 3
    let some simple ← checkSource .simple simplePath | return 3
    let some es ← checkSource .es esPath | return 3
    IO.println ((Json.mkObj [
      ("schema", toJson ("slr.gwb-controlled-office-evaluation.v1" : String)),
      ("views", Json.arr #[en,simple,es]),
      ("bounded_rule_only", toJson true),
      ("native_attachment_paid", toJson false),
      ("referee_authority_paid", toJson false),
      ("world_truth_paid", toJson false)]).compress)
    return 0
  | _ => return 2

