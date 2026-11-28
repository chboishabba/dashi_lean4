import RequestProject.Slr.GwbMultilingualOffice
open Lean
open Wikidata.Slr.GwbMultilingualOffice
open Wikidata.Slr.WorldSemanticFibre

def parseEdition : String → Option Edition
  | "en" => some .en
  | "simple" => some .simple
  | "es" => some .es
  | _ => none

def parseConsumer : String → Option OfficeConsumer
  | "query:gwb:office-years:v1" => some .years
  | "query:gwb:office-days:v1" => some .days
  | _ => none

def supportJson : Option Support → Json
  | none => Json.null
  | some s => Json.mkObj [("positive", toJson s.positive), ("negative", toJson s.negative)]

def digestFile (path : String) : IO (Option String) := do
  let r ← IO.Process.output { cmd := "sha256sum", args := #[path] }
  let sha := (r.stdout.splitOn " ").head!
  return if r.exitCode == 0 && sha.length == 64 then some sha else none

def main (args : List String) : IO UInt32 := do
  match args with
  | [le, lp, re, rp, query] =>
    let some l ← pure (parseEdition le) | return 2
    let some r ← pure (parseEdition re) | return 2
    let some q ← pure (parseConsumer query) | return 2
    if l = r then return 2
    let a : Source := (l, ← IO.FS.readFile lp)
    let b : Source := (r, ← IO.FS.readFile rp)
    let some ld ← digestFile lp | return 3
    let some rd ← digestFile rp | return 3
    if ha : a.2.startsWith (lead a.1) = true then
      if hb : b.2.startsWith (lead b.1) = true then
        if pa : predicateMatches a = true then
          if pb : predicateMatches b = true then
            have exactAnswer := exactPairAnswer a b q ha hb pa pb
            let result := (attachedAnswer a q.query, attachedAnswer b q.query)
            if result != (expectedSupport l q, expectedSupport r q) then return 3
            let (ls,lt,ll) := occurrence l
            let (rs,rt,rl) := occurrence r
            IO.println ((Json.mkObj [
              ("schema", toJson ("slr.gwb-golden-pair-evaluation.v1" : String)),
              ("theorem", toJson ("Wikidata.Slr.GwbMultilingualOffice.exactPairAnswer" : String)),
              ("query_ref", toJson query),
              ("left", Json.mkObj [("edition",toJson le),("source_sha256",toJson ld),
                ("predicate_span",toJson [ls,lt]),("predicate",toJson ll)]),
              ("right", Json.mkObj [("edition",toJson re),("source_sha256",toJson rd),
                ("predicate_span",toJson [rs,rt]),("predicate",toJson rl)]),
              ("answer", Json.mkObj [("schema",toJson ("slr.signed-view-query-answer.v1" : String)),
                ("query_ref",toJson query),("left_support",supportJson result.1),
                ("right_support",supportJson result.2)]),
              ("bounded_rule_only",toJson true),("world_truth_paid",toJson false),
              ("referee_authority_paid",toJson false)]).compress)
            return 0
          else return 3
        else return 3
      else return 3
    else return 3
  | _ => return 2
