import Lean

/-!
GWB M2: real SLR named-topic *source-local* inference, not a QID or
unrestricted natural-language truth theorem.

The original native SLR derives the answer from full original source
reinspection and native parser PERSON groups, never nearest-token distance.
This independent checker recomputes the singular named PERSON group and
requires two DISTINCT original supporting statement references. Thus a
source-local positive linguistic answer is available while S29 remains
Pending. Original owner semantic admission and world QID stay separate.

Do not interpret this module as a proof that no conceivable alternate
literary reading exists or that a human semantic reviewer accepted it.
-/
open Lean

namespace Wikidata.Slr.GwbNamedTopicPolicy

private def getString (j : Json) (field : String) : String :=
  (j.getObjValAs? String field).toOption.getD ""

private def getBool (j : Json) (field : String) : Bool :=
  (j.getObjValAs? Bool field).toOption.getD false

private def getNat (j : Json) (field : String) : Nat :=
  (j.getObjValAs? Nat field).toOption.getD 0

private def getArray (j : Json) (field : String) : Array Json :=
  (j.getObjValAs? (Array Json) field).toOption.getD #[]

private def subobj (j : Json) (field : String) : Json :=
  (j.getObjVal? field).toOption.getD Json.null

private def names (native : Json) : List String :=
  (getArray native "nominations").toList.filterMap (fun row =>
    if getString row "observation_kind" == "parser_entity" &&
       getString row "parser_pos_or_label" == "PERSON" then
      some (getString row "surface")
    else none)

/-- Source-local named-topic admissibility is deliberately narrower than
    complete coreference. It is exactly what the original Rust policy
    claims for this *specific* original book and focus. -/
def checkSourceLocalPolicy
    (inspect frontier answer : Json) : Bool :=
  let focus := subobj inspect "focus"
  let candidate := subobj inspect "candidate_antecedent"
  let actualNames := names frontier
  let namedPersonNames := actualNames.eraseDups
  let actualStatements :=
    (getArray frontier "nominations").toList.filterMap (fun row =>
      if getString row "observation_kind" == "parser_entity" &&
         getString row "parser_pos_or_label" == "PERSON" then
        some (getString row "original_statement_ref")
      else none)
  let supports := getArray answer "supporting_person_mentions"
  let independentStatements :=
    (supports.toList.map (fun row => getString row "statement_ref")).eraseDups
  let originalBefore := getArray inspect "before"
  let selected := getString candidate "surface"
  let allNamedSame :=
    actualNames.all (fun n => n == selected)
  getString inspect "schema" == "slr-native-antecedent-s29-inspection-v1" &&
  getString frontier "schema" == "slr-native-antecedent-bounded-frontier-v1" &&
  getString answer "schema" == "slr-native-named-topic-inference-v1" &&
  getString answer "policy_ref" ==
    "slr:policy:source-local-repeated-person-topic:v1" &&
  getString frontier "canonical_content_sha256" ==
    "7ff2ec8ffe6243871ad682e7d7060fe3b84025fb15dbe229154d7aa7f6a72b30" &&
  getString frontier "canonical_content_sha256" ==
    getString inspect "canonical_content_sha256" &&
  getString frontier "source_revision_ref" ==
    getString inspect "source_revision_ref" &&
  getString answer "original_source_revision_ref" ==
    getString inspect "source_revision_ref" &&
  getString answer "original_document_ref" ==
    getString inspect "document_ref" &&
  getString answer "parser_run_ref" ==
    getString frontier "parser_run_ref" &&
  getString answer "focus_mention_ref" ==
    getString frontier "focus_mention_ref" &&
  getString answer "review_item_ref" ==
    getString inspect "review_item_ref" &&
  getString answer "s29_status_at_derivation" ==
    getString inspect "s29_review_status" &&
  getString focus "surface" == "he" &&
  getString frontier "focus_parser_pos" == "PRON" &&
  getNat focus "start_char" == 4534 &&
  getNat focus "end_char" == 4536 &&
  getString candidate "surface" == "Bush" &&
  getNat candidate "start_char" == 4310 &&
  getNat candidate "end_char" == 4314 &&
  getString frontier "nominated_source_anchor_ref" ==
    getString candidate "statement_ref" &&
  getNat frontier "nominated_source_anchor_start_char" == 4310 &&
  getNat frontier "nominated_source_anchor_end_char" == 4314 &&
  getString answer "status" == "DERIVED_SOURCE_LOCAL_NAMED_TOPIC" &&
  getString answer "source_local_answer" == "Bush" &&
  getBool answer "source_local_inference_derived" &&
  !(getBool answer "requires_human_s29_to_form_policy_inference") &&
  !(getBool answer "governed_source_local_admission_paid") &&
  !(getBool answer "complete_all_live_referents_proven") &&
  !(getBool answer "external_qid_paid") &&
  !(getBool answer "historical_claim_truth_paid") &&
  getNat answer "raw_parser_observation_count" ==
    (getArray frontier "nominations").size &&
  getNat answer "named_person_observation_count" ==
    actualNames.length &&
  getNat answer "distinct_named_person_groups" == 1 &&
  getNat answer "distinct_supporting_original_sentences" ==
    independentStatements.length &&
  getNat answer "distinct_supporting_original_sentences" >= 2 &&
  getNat answer "named_person_observation_count" >= 2 &&
  actualStatements.eraseDups.length >= 2 &&
  namedPersonNames == ["Bush"] &&
  allNamedSame &&
  supports.size == actualNames.length &&
  originalBefore.size == 4

structure CheckedSourceLocalPolicy
    (inspect frontier answer : Json) where
  checked : checkSourceLocalPolicy inspect frontier answer = true

/-- This theorem transports the actual structural checker to the kernel.
    It is NOT the independent human/typed semantic admission theorem. -/
theorem checked_policy_source_local
    {inspection frontier policy : Json}
    (checked : CheckedSourceLocalPolicy inspection frontier policy) :
    checkSourceLocalPolicy inspection frontier policy = true :=
  checked.checked

/-- Source-local policy inference does not assert external referent equality.
    In particular the two distinct QIDs remain separate. -/
theorem q207_not_q23505 :
    ("Q207" : String) ≠ "Q23505" := by decide

end Wikidata.Slr.GwbNamedTopicPolicy

def main (args : List String) : IO UInt32 := do
  match args with
  | [inspectionPath, frontierPath, answerPath] =>
    let i ← IO.FS.readFile inspectionPath
    let f ← IO.FS.readFile frontierPath
    let a ← IO.FS.readFile answerPath
    match Json.parse i, Json.parse f, Json.parse a with
    | .ok inspect, .ok frontier, .ok answer =>
      if h : Wikidata.Slr.GwbNamedTopicPolicy.checkSourceLocalPolicy
          inspect frontier answer = true then
        let _proof : Wikidata.Slr.GwbNamedTopicPolicy.CheckedSourceLocalPolicy
            inspect frontier answer := ⟨h⟩
        IO.println "GWB_NAMED_TOPIC_LINGUISTIC_POLICY_KERNEL_OK"
        IO.println "Source-local Bush interpretation derived under explicit native discourse policy"
        IO.println "Original typed scope and governed admission remain distinct; Q23505 and Q207 unpaid"
        return 0
      else
        IO.eprintln "GWB_NAMED_TOPIC_POLICY_REJECTED: source/PERSON/continuity/authority mismatch"
        return 1
    | _, _, _ =>
      IO.eprintln "GWB_NAMED_TOPIC_POLICY_REJECTED: original JSON input is malformed"
      return 1
  | _ =>
    IO.eprintln "usage: lake env lean --run GwbNamedTopicPolicy.lean INSPECTION FRONTIER POLICY"
    return 2

#print axioms Wikidata.Slr.GwbNamedTopicPolicy.checked_policy_source_local
#print axioms Wikidata.Slr.GwbNamedTopicPolicy.q207_not_q23505
