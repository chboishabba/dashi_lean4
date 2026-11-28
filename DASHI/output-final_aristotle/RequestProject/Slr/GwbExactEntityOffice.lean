import RequestProject.Slr.GwbWorldGraphProof
import RequestProject.Slr.GwbMultilingualOffice

namespace Wikidata.Slr.GwbExactEntityOffice
open Lean
open GwbWorldGraph

private def get (j : Json) (k : String) : Json :=
  (j.getObjVal? k).toOption.getD Json.null
private def str (j : Json) (k : String) : Option String :=
  (j.getObjValAs? String k).toOption
private def nat (j : Json) (k : String) : Option Nat :=
  (j.getObjValAs? Nat k).toOption
private def arr (j : Json) (k : String) : List Json :=
  ((j.getObjValAs? (Array Json) k).toOption.getD #[]).toList
private def exactQualifier (row : Json) (property datatype : String) : Option Json :=
  match arr (get row "qualifiers") property with
  | [s] => if str s "property" == some property &&
      str s "snaktype" == some "value" && str s "datatype" == some datatype
    then some (get s "datavalue") else none
  | _ => none

def dateMatches (row : Json) (property time : String) : Bool :=
  match exactQualifier row property "time" with
  | none => false
  | some d =>
    let v := get d "value"
    str d "type" == some "time" && str v "time" == some time &&
    nat v "precision" == some 11 && nat v "timezone" == some 0 &&
    nat v "before" == some 0 && nat v "after" == some 0 &&
    str v "calendarmodel" == some "http://www.wikidata.org/entity/Q1985727"

def ordinalMatches (row : Json) : Bool :=
  match exactQualifier row "P1545" "string" with
  | none => false
  | some d => str d "type" == some "string" && str d "value" == some "43"

def exactOfficeRow (row : Json) : Bool :=
  let s := get row "mainsnak"
  let d := get s "datavalue"
  let v := get d "value"
  yearIntervalStatementMatches "P39" "Q11696" 2001 2009 row &&
  (match str row "id" with
    | some id => id.toLower.startsWith "q207$" && decide (id.length > 5)
    | none => false) &&
  str s "datatype" == some "wikibase-item" &&
  str d "type" == some "wikibase-entityid" &&
  str v "entity-type" == some "item" && nat v "numeric-id" == some 11696 &&
  ordinalMatches row &&
  dateMatches row "P580" "+2001-01-20T00:00:00Z" &&
  dateMatches row "P582" "+2009-01-20T00:00:00Z"

def exactOfficeRows (entity : Json) : List Json :=
  (originalPropertyRows entity "Q207" "P39").filter exactOfficeRow

theorem exactOfficeRowsSound (entity row : Json) :
    row ∈ exactOfficeRows entity ↔
    row ∈ originalPropertyRows entity "Q207" "P39" ∧ exactOfficeRow row = true := by
  simp [exactOfficeRows, List.mem_filter]

def exactOfficeWitness (entity : Json) : Option Json :=
  match exactOfficeRows entity with
  | [row] => some row
  | _ => none

theorem witnessSameOriginalRow (entity row : Json)
    (h : exactOfficeWitness entity = some row) :
    row ∈ originalPropertyRows entity "Q207" "P39" ∧ exactOfficeRow row = true := by
  apply (exactOfficeRowsSound entity row).mp
  unfold exactOfficeWitness at h
  cases he : exactOfficeRows entity with
  | nil => simp [he] at h
  | cons a rest =>
    cases rest with
    | nil =>
      simp [he] at h
      simp [he, h]
    | cons b bs => simp [he] at h

end Wikidata.Slr.GwbExactEntityOffice

#print axioms Wikidata.Slr.GwbExactEntityOffice.witnessSameOriginalRow
