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
  let .ok json := Json.parse raw
    | do
      IO.eprintln "REL_OBSERVED_MEET_REJECTED: JSON"
      return 1
  let some (sources, fibre) := decodeReceipt json
    | do
      IO.eprintln "REL_OBSERVED_MEET_REJECTED: typed source inventory"
      return 1
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
      if FiniteConsumer.checkConstant sources (fun source => observed source c) then
        IO.eprintln "REL_OBSERVED_MEET_REJECTED: distinct answer missing"
        return 1
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

/-- Query all original recorded relations or one exact relation type.
    No semantic entailment is inferred from a missing recorded row. -/
def selectedRelation (kind : String) (row : Json) : Bool :=
  kind == "all" || str row "type" == some kind

def selectRelations (kind : String) (original : List Json) : List Json :=
  original.filter (selectedRelation kind)

theorem selectedRelationExact (kind : String) (original : List Json) (row : Json) :
    row ∈ selectRelations kind original ↔
      row ∈ original ∧ selectedRelation kind row = true := by
  simp [selectRelations, List.mem_filter]

/-- The exact source inventory and result are kept separate from all-live
    completeness. The original packet is independently reopened by SLR. -/
def checkRecordedRelationQuery (reopened answer : Json) : Bool := Id.run do
  let some packet := obj reopened "packet" | return false
  let some comparison := obj packet "comparison" | return false
  let some bundle := obj comparison "bundle" | return false
  let some original := rows bundle "relations" | return false
  let some returned := rows answer "answers" | return false
  let some kind := str answer "query_relation_type" | return false
  let actual := returned.map (fun row => obj row "original_relation")
  let expected := (selectRelations kind original).map some
  return str reopened "schema" == some "slr-reopened-original-relation-packet-v1" &&
    str answer "schema" == some "slr.original-relation-query.v1" &&
    nonblank kind &&
    (["numeric_run_ref","document_ref","snapshot_ref","packet_sha256"] : List String).all
      (fun k => (str reopened k).isSome && str reopened k == str answer k) &&
    nat answer "recorded_relation_count" == some original.length &&
    nat answer "answer_count" == some returned.length &&
    actual == expected &&
    (answer.getObjValAs? Bool "all_live_semantic_readings_covered").toOption == some false &&
    (answer.getObjValAs? Bool "governed_identity_paid").toOption == some false &&
    (answer.getObjValAs? Bool "level_three_paid").toOption == some false &&
    (answer.getObjValAs? Bool "world_truth_paid").toOption == some false

def runRecordedRelationQuery (packetPath answerPath : String) : IO UInt32 := do
  match Json.parse (← IO.FS.readFile packetPath), Json.parse (← IO.FS.readFile answerPath) with
  | .ok packet, .ok answer =>
    if h : checkRecordedRelationQuery packet answer = true then
      let _ := h
      IO.println "REL_ORIGINAL_RECORDED_QUERY_CHECKED"
      return 0
    else
      IO.eprintln "REL_ORIGINAL_RECORDED_QUERY_REJECTED"
      return 1
  | _, _ =>
    IO.eprintln "REL_ORIGINAL_RECORDED_QUERY_REJECTED: JSON"
    return 1

/-- Recompute the native coordinate projection directly from the original
factor alternatives; absent and explicit null are distinct. -/
def factorOutcome (axis : String) (alternative : Json) : Json :=
  let selected := if axis == "type_ref" || axis == "value" then obj alternative axis
    else (obj alternative "value").bind (fun v => obj v axis)
  Json.mkObj [("present", toJson selected.isSome), ("value", selected.getD Json.null)]

def factorChoice (axis : String) (alternative : Json) : Json :=
  Json.mkObj [("alternative_ref", (obj alternative "alternative_ref").getD Json.null),
    ("outcome", factorOutcome axis alternative)]

def checkFactorRow (axis : String) (original row : Json) : Bool := Id.run do
  let some alternatives := rows original "alternatives" | return false
  let some first := alternatives.head? | return false
  let some reported := rows row "choices" | return false
  let choices := alternatives.map (factorChoice axis)
  let outcomes := (alternatives.map (factorOutcome axis)).foldl
    (fun acc value => if acc.contains value then acc else acc ++ [value]) []
  let constant := FiniteConsumer.checkConstant alternatives
    (fun a => (factorOutcome axis a).compress)
  let separator := match alternatives.find? (fun a =>
      (factorOutcome axis a).compress != (factorOutcome axis first).compress) with
    | none => Json.null
    | some other => Json.mkObj [("left", factorChoice axis first), ("right", factorChoice axis other)]
  return (["factor_ref","factor_type","closure_state","residuals"] : List String).all
      (fun k => (obj original k).isSome && obj original k == obj row k) &&
    obj original "metadata" == obj row "source_metadata" &&
    obj original "constraints" == obj row "embedded_constraints" &&
    alternatives.all (fun a => (str a "alternative_ref").isSome) &&
    choices == reported && rows row "outcomes" == some outcomes &&
    obj row "represented_separator" == some separator &&
    (row.getObjValAs? Bool "recorded_product_constant").toOption == some constant &&
    (row.getObjValAs? Bool "admissible_separator_proven").toOption == some false

def checkFactorProjection (native receipt : Json) : Bool := Id.run do
  let some packet := obj native "packet" | return false
  let some comparison := obj packet "comparison" | return false
  let some reduction := obj comparison "reduction_projection" | return false
  let some factors := rows reduction "factors" | return false
  let some reported := rows receipt "rows" | return false
  let some axis := str receipt "consumer_axis" | return false
  return str native "schema" == some "slr-reopened-original-relation-packet-v1" &&
    str receipt "schema" == some "slr.recorded-factor-consumer.v1" &&
    (["type_ref","referential_type","role","value"] : List String).contains axis &&
    (["numeric_run_ref","document_ref","snapshot_ref","packet_sha256"] : List String).all
      (fun k => (str native k).isSome && str native k == str receipt k) &&
    (["source_revision_ref","parser_run_ref"] : List String).all
      (fun k => (str comparison k).isSome && str comparison k == str receipt k) &&
    nat receipt "factor_count" == some factors.length &&
    factors.length == reported.length &&
    (factors.zip reported).all (fun pair => checkFactorRow axis pair.1 pair.2) &&
    (["missing_original_tags","prefix_uncovered_nonwhitespace"] : List String).all
      (fun k => (obj packet k).isSome && obj packet k == obj receipt k) &&
    (["semantic_coverage_paid","source_meaning_correspondence_paid","governed_identity_paid",
      "level_three_paid","world_truth_paid"] : List String).all
      (fun k => (receipt.getObjValAs? Bool k).toOption == some false) &&
    (receipt.getObjValAs? Bool "outside_model_possible").toOption == some true

theorem recordedFactorConstancy (axis : String) (alternatives : List Json)
    (h : FiniteConsumer.checkConstant alternatives
      (fun a => (factorOutcome axis a).compress) = true) :
    ∀ a ∈ alternatives, ∀ b ∈ alternatives,
      (factorOutcome axis a).compress = (factorOutcome axis b).compress :=
  FiniteConsumer.checkConstant_sound alternatives
    (fun a => (factorOutcome axis a).compress) h

def runFactorProjection (packetPath receiptPath : String) : IO UInt32 := do
  match Json.parse (← IO.FS.readFile packetPath), Json.parse (← IO.FS.readFile receiptPath) with
  | .ok packet, .ok receipt =>
    if checkFactorProjection packet receipt then
      IO.println "REL_RECORDED_FACTOR_CONSUMER_CHECKED"
      return 0
    else
      IO.eprintln "REL_RECORDED_FACTOR_CONSUMER_REJECTED"
      return 1
  | _, _ =>
    IO.eprintln "REL_RECORDED_FACTOR_CONSUMER_REJECTED: JSON"
    return 1

private def intField (j : Json) (k : String) : Option Int :=
  (j.getObjValAs? Int k).toOption

private def demandKey (j : Json) : Option (Nat × Nat) := do
  pure (← nat j "target_kind", ← nat j "target_id")

/-- Independent accounting on the original signed numeric demand input.
Every represented candidate survives in the upper envelope, including a
reported refutation. This is not a proof that the represented domain covers
production-live semantics. -/
def checkDemandInventory (receipt : Json) : Bool := Id.run do
  let some universe := rows receipt "represented_universe" | return false
  let some candidates := rows receipt "candidates" | return false
  let some oldEvidence := rows receipt "historical_evidence" | return false
  let some current := rows receipt "current_evidence" | return false
  let some horizon := rows receipt "signed_horizon_tallies" | return false
  let some demand := nat receipt "demand_id" | return false
  let some original := obj receipt "original_demand" | return false
  let some keys := universe.mapM demandKey | return false
  let some actual := candidates.mapM demandKey | return false
  let some evidenceIds := current.mapM (fun e => nat e "evidence_id") | return false
  let candidateExact := (candidates.zip keys).all fun (c, k) =>
    match obj c "state" with
    | none => false
    | some s =>
      let currentMatch := current.any fun e =>
        nat e "evidence_id" == nat s "admissibility_evidence_id" &&
        (nat e "evidence_id").isSome && demandKey e == some k
      demandKey s == some k &&
      nat s "demand_id" == some demand &&
      (c.getObjValAs? Bool "reported_refuted").toOption ==
        (s.getObjValAs? Bool "refuted").toOption &&
      (c.getObjValAs? Bool "same_candidate_current_evidence").toOption == some currentMatch &&
      (c.getObjValAs? Bool "retained_in_conservative_envelope").toOption == some true
  let horizonExact := keys.all fun k =>
    ([3,6,9] : List Nat).all fun h =>
      let evidence := current.filter fun e =>
        demandKey e == some k && (nat e "horizon").isSome &&
        decide ((nat e "horizon").getD 10 ≤ h)
      let total := evidence.foldl (fun sum e => sum + (intField e "signed_residual").getD 0) (0 : Int)
      let phase : Int := if total < 0 then -1 else if total > 0 then 1 else 0
      match horizon.filter (fun row => demandKey row == some k && nat row "horizon" == some h) with
      | [row] => nat row "demand_id" == some demand &&
          nat row "evidence_count" == some evidence.length &&
          intField row "signed_residual" == some total && intField row "phase" == some phase
      | _ => false
  return str receipt "schema" == some "slr.native-demand-fibre.v1" &&
    nat original "demand_id" == some demand && decide (demand > 0) &&
    keys == actual && decide keys.Nodup && decide evidenceIds.Nodup &&
    universe.all (fun row => nat row "demand_id" == some demand) &&
    candidateExact &&
    (receipt.getObjValAs? Bool "current_authority_view_installed").toOption == some true &&
    current.all (fun e => oldEvidence.contains e &&
      nat e "demand_id" == some demand && (intField e "signed_residual").isSome &&
      (nat e "horizon").isSome) &&
    horizon.length == keys.length * 3 && horizonExact &&
    (["semantic_coverage_paid","source_meaning_correspondence_paid","governed_identity_paid",
      "level_three_paid","world_truth_paid","outside_model_discharge_paid"] : List String).all
      (fun k => (receipt.getObjValAs? Bool k).toOption == some false)

def runDemandInventory (path : String) : IO UInt32 := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok receipt =>
    if checkDemandInventory receipt then
      IO.println "REL_NATIVE_DEMAND_INVENTORY_CHECKED"
      return 0
    else
      IO.eprintln "REL_NATIVE_DEMAND_INVENTORY_REJECTED"
      return 1
  | .error _ =>
    IO.eprintln "REL_NATIVE_DEMAND_INVENTORY_REJECTED: JSON"
    return 1

end Wikidata.Slr.RelationalObservedMeet
