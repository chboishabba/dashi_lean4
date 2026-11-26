import RequestProject.Slr.FiniteConsumerCertificate
import Lean.Data.Json

/-!
The native SLR family is a selected finite source-observation inventory.
This checker reconstructs its typed incidence transpose independently, using
the original selected observation rows, not Rust's reported common flags.
This is the finite recorded-coordinate consumer, not a semantic live-fibre
enumeration or a claim of independent source truth. Reuses the golden
FiniteConsumerCertificate and DocumentQuerySound proof owners.
-/
namespace Wikidata.Slr.RelationalObservedMeet
open Lean

structure Coordinate where
  axis : String
  slot : String
  occurrence : Nat
  valueRef : String
deriving DecidableEq, Repr

structure SelectedSource where
  selectorRef : String
  observationRef : String
  revisionRef : String
  coordinates : List Coordinate
deriving DecidableEq, Repr

structure FibreRow where
  coordinate : Coordinate
  presentIn : List String
  notRecordedIn : List String
deriving DecidableEq, Repr

private def str (j : Json) (k : String) : Option String :=
  (j.getObjValAs? String k).toOption

private def nat (j : Json) (k : String) : Option Nat :=
  (j.getObjValAs? Nat k).toOption

private def obj (j : Json) (k : String) : Option Json :=
  (j.getObjVal? k).toOption

private def rows (j : Json) (k : String) : Option (List Json) :=
  ((j.getObjValAs? (Array Json) k).toOption).map Array.toList

private def strings (j : Json) (k : String) : Option (List String) :=
  ((j.getObjValAs? (Array String) k).toOption).map Array.toList

private def nonblank (s : String) : Bool :=
  !s.toList.all Char.isWhitespace

private def coordinate? (axis slot : String) (occurrence : Nat)
    (value : String) : Option Coordinate :=
  if nonblank value then some ⟨axis, slot, occurrence, value⟩ else none

private def role? (axis valueKey : String) (j : Json) : Option Coordinate := do
  coordinate? axis (← str j "role_ref") (← nat j "occurrence") (← str j valueKey)

private def contextCoordinate? (ctx : Json) (slot : String) :
    Option (Option Coordinate) := do
  match ← obj ctx (slot ++ "_ref") with
  | .null => pure none
  | .str v => pure (coordinate? "context" slot 0 v)
  | _ => none

def decodeSelected (j : Json) : Option SelectedSource := do
  let selector ← str j "selector_ref"
  let o ← obj j "observation"
  let observation ← str o "observation_ref"
  let revision ← str o "source_revision_ref"
  let predicate ← coordinate? "predicate" "predicate" 0 (← str o "predicate_candidate_ref")
  let roles ← (← rows o "role_bindings").mapM (role? "role" "filler_candidate_ref")
  let types ← (← rows o "role_type_hypotheses").mapM (role? "role_type" "candidate_type_ref")
  let candidateTypes ← strings o "candidate_type_refs"
  let ctx ← obj o "context"
  let context ← (["scope","time","modality","quantifier","attribution","ontology","language"]
    : List String).mapM (contextCoordinate? ctx)
  if !nonblank selector || !nonblank observation || !nonblank revision then none
  else
    pure ⟨selector, observation, revision,
      [predicate] ++ roles ++ types ++
      candidateTypes.filterMap (coordinate? "candidate_type" "type" 0) ++
      context.filterMap id⟩

def decodeFibreRow (j : Json) : Option FibreRow := do
  let c ← obj j "coordinate"
  let coordinate ← coordinate? (← str c "axis") (← str c "slot")
    (← nat c "occurrence") (← str c "value_ref")
  pure ⟨coordinate, (← strings j "present_in"), (← strings j "not_recorded_in")⟩

/-- This membership query is deliberately about the recorded coordinate. -/
def observed (s : SelectedSource) (c : Coordinate) : Bool :=
  decide (c ∈ s.coordinates)

def checkMembership (sources : List SelectedSource) (r : FibreRow) : Bool :=
  sources.all fun s =>
    decide (observed s r.coordinate = decide (s.selectorRef ∈ r.presentIn)) &&
    decide ((!observed s r.coordinate) = decide (s.selectorRef ∈ r.notRecordedIn))

theorem checkedMembershipSound
    (sources : List SelectedSource) (r : FibreRow)
    (h : checkMembership sources r = true) :
    ∀ s ∈ sources,
      observed s r.coordinate = decide (s.selectorRef ∈ r.presentIn) ∧
      (!observed s r.coordinate) = decide (s.selectorRef ∈ r.notRecordedIn) := by
  simp only [checkMembership, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

def checkFibreRow (sources : List SelectedSource) (r : FibreRow) : Bool :=
  let selectors := sources.map (·.selectorRef)
  !r.presentIn.isEmpty &&
  decide r.presentIn.Nodup && decide r.notRecordedIn.Nodup &&
  r.presentIn.all (fun s => decide (s ∈ selectors)) &&
  r.notRecordedIn.all (fun s => decide (s ∈ selectors)) &&
  checkMembership sources r

def checkInventory (sources : List SelectedSource) (fibre : List FibreRow) : Bool :=
  let keys := fibre.map (·.coordinate)
  decide (2 ≤ sources.length ∧ sources.length ≤ 10) &&
  decide (sources.map (·.selectorRef)).Nodup &&
  decide (sources.map (·.observationRef)).Nodup &&
  decide (sources.map (·.revisionRef)).Nodup &&
  decide keys.Nodup &&
  fibre.all (checkFibreRow sources) &&
  sources.all (fun s => s.coordinates.all (fun c => decide (c ∈ keys)))

/-- An exact source-only common answer has no hidden semantic premise.
The complete domain for this query is the selected source inventory,
not all interpretations of the underlying text. -/
def commonObserved (sources : List SelectedSource) (c : Coordinate) : Bool :=
  sources.all (fun s => observed s c)

theorem commonObservedSound
    (sources : List SelectedSource) (c : Coordinate)
    (h : commonObserved sources c = true) :
    ∀ s ∈ sources, observed s c = true := by
  simpa only [commonObserved, List.all_eq_true] using h

theorem checkedCommonConsumerConstant
    (sources : List SelectedSource) (c : Coordinate)
    (h : FiniteConsumer.checkConstant sources (fun s => observed s c) = true) :
    ∀ x ∈ sources, ∀ y ∈ sources, observed x c = observed y c :=
  FiniteConsumer.checkConstant_sound sources (fun s => observed s c) h

/-- Two selected sources distinguish the recorded-coordinate query.
Absence in a source is not a counterclaim about the world. -/
theorem differentRecordedAnswersBlockConstant
    (sources : List SelectedSource) (c : Coordinate)
    (x y : SelectedSource) (hx : x ∈ sources) (hy : y ∈ sources)
    (different : observed x c ≠ observed y c) :
    FiniteConsumer.checkConstant sources (fun s => observed s c) ≠ true := by
  intro h
  exact different (checkedCommonConsumerConstant sources c h x hx y hy)

def decodeReceipt (j : Json) : Option (List SelectedSource × List FibreRow) := do
  let projection ← obj j "projection"
  if str projection "schema" != some "itir.relational-family.v2" then none
  else
    let sources ← (← rows projection "sources").mapM decodeSelected
    let fibre ← (← rows projection "observed_coordinate_meet").mapM decodeFibreRow
    pure (sources, fibre)

def run (inputPath outputPath : String) : IO UInt32 := do
  let raw ← IO.FS.readFile inputPath
  let .ok json := Json.parse raw | IO.eprintln "REL_OBSERVED_MEET_REJECTED: JSON"; return 1
  let some (sources, fibre) := decodeReceipt json
    | IO.eprintln "REL_OBSERVED_MEET_REJECTED: typed source inventory"; return 1
  if !checkInventory sources fibre then
    IO.eprintln "REL_OBSERVED_MEET_REJECTED: missing, extra or wrong incidence"
    return 1
  let mut commonCount : Nat := 0
  let mut differenceCount : Nat := 0
  for row in fibre do
    let c := row.coordinate
    if h : commonObserved sources c = true then
      let _ := commonObservedSound sources c h
      if hConst : FiniteConsumer.checkConstant sources (fun s => observed s c) = true then
        let _ := checkedCommonConsumerConstant sources c hConst
        commonCount := commonCount + 1
      else
        IO.eprintln "REL_OBSERVED_MEET_REJECTED: common answer inconsistent"
        return 1
    else
      differenceCount := differenceCount + 1
  let sha ← IO.Process.output { cmd := "sha256sum", args := #[inputPath] }
  if sha.exitCode != 0 || (← IO.FS.readFile inputPath) != raw then
    IO.eprintln "REL_OBSERVED_MEET_REJECTED: digest/readback"
    return 1
  IO.FS.writeFile outputPath ((Json.mkObj [
    ("schema", toJson ("itir.checked-observed-coordinate-meet.v1" : String)),
    ("native_receipt_sha256", toJson ((sha.stdout.splitOn " ").head!)),
    ("selected_source_count", toJson sources.length),
    ("coordinate_count", toJson fibre.length),
    ("common_recorded_coordinate_count", toJson commonCount),
    ("different_recorded_coordinate_count", toJson differenceCount),
    ("selected_inventory_incidence_checked", toJson true),
    ("all_live_semantic_readings_covered", toJson false),
    ("semantic_equivalence_paid", toJson false),
    ("world_truth_paid", toJson false)]).pretty ++ "\n")
  IO.println s!"REL_OBSERVED_MEET_CHECKED sources={sources.length} common={commonCount} different={differenceCount}"
  return 0

end Wikidata.Slr.RelationalObservedMeet
