import RequestProject.Slr.GwbMultilingualOffice
open Wikidata.Slr.GwbMultilingualOffice
open Wikidata.Slr.WorldSemanticFibre

def main (args : List String) : IO UInt32 := do
  match args with
  | [enPath, simplePath, esPath] =>
    let en ← IO.FS.readFile enPath
    let simple ← IO.FS.readFile simplePath
    let es ← IO.FS.readFile esPath
    let sources : List Source := [(.en, en), (.simple, simple), (.es, es)]
    if !sources.all (fun s => s.2.startsWith (lead s.1)) then
      IO.eprintln "GWB_CONTROLLED_LEAD_HELD"
      return 3
    if !(sources.all (fun s => decide (answer s yearQuery = some (support .positive)))) ||
       !(decide (answer (.en, en) dayQuery = none ∧ answer (.simple, simple) dayQuery = none ∧
          answer (.es, es) dayQuery = some (support .positive))) then
      return 1
    IO.println "GWB_CONTROLLED_OFFICE_RULE_OK; source attachment and referee not paid"
    return 0
  | _ => return 2
