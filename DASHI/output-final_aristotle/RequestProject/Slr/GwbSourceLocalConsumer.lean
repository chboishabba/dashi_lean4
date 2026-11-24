import Lean

/-!
P0 original source-local consumer certificate.

This is an original-source/revision bound, versioned named-topic linguistic
answer, not unrestricted English semantics or a witnessed Level-3 identity.
Python independently audits all original supporting spans and fields.
-/
open Lean

namespace Wikidata.Slr.GwbSourceLocalConsumer

private def field (j : Json) (k : String) : String :=
  (j.getObjValAs? String k).toOption.getD ""

private def yes (j : Json) (k : String) : Bool :=
  (j.getObjValAs? Bool k).toOption.getD false

private def number (j : Json) (k : String) : Nat :=
  (j.getObjValAs? Nat k).toOption.getD 0

private def sub (j : Json) (k : String) : Json :=
  (j.getObjVal? k).toOption.getD Json.null

private def arr (j : Json) (k : String) : Array Json :=
  (j.getObjValAs? (Array Json) k).toOption.getD #[]

private def spanIs (j : Json) (start finish : Nat) : Bool :=
  match (j.getArr?).toOption with
  | some xs => xs.size == 2 &&
      (xs[0]?.getD Json.null).getNat?.toOption == some start &&
      (xs[1]?.getD Json.null).getNat?.toOption == some finish
  | none => false

private def coherentSource
    (inspection frontier inference consumer replay : Json) : Bool :=
  let focus := sub inspection "focus"
  let candidate := sub inspection "candidate_antecedent"
  let replayAnswer := sub replay "current"
  let support := arr consumer "original_person_support"
  field inspection "schema" == "slr-native-antecedent-s29-inspection-v1" &&
  field frontier "schema" == "slr-native-antecedent-bounded-frontier-v1" &&
  field inference "schema" == "slr-native-named-topic-inference-v1" &&
  field consumer "schema" == "slr-native-source-local-consumer-v1" &&
  field replay "schema" == "slr-native-source-local-answer-replay-v1" &&
  field consumer "consumer_scope_ref" ==
    "source-local-antecedent-query:declared-named-topic-policy-v1" &&
  field consumer "source_content_sha256" ==
    "7ff2ec8ffe6243871ad682e7d7060fe3b84025fb15dbe229154d7aa7f6a72b30" &&
  field consumer "source_content_sha256" ==
    field inspection "canonical_content_sha256" &&
  field consumer "source_document_ref" ==
    field inspection "document_ref" &&
  field consumer "source_revision_ref" ==
    field inspection "source_revision_ref" &&
  field consumer "original_parser_run_ref" ==
    field frontier "parser_run_ref" &&
  field consumer "original_candidate_set_ref" ==
    field frontier "candidate_set_ref" &&
  field consumer "original_focus_mention_ref" ==
    field focus "mention_ref" &&
  field consumer "original_focus_statement_ref" ==
    field focus "statement_ref" &&
  field consumer "original_focus_region_ref" ==
    field focus "region_ref" &&
  field consumer "original_focus_surface" == "he" &&
  spanIs (sub consumer "original_focus_span") 4534 4536 &&
  field consumer "original_selected_antecedent_statement_ref" ==
    field candidate "statement_ref" &&
  field consumer "original_selected_antecedent_region_ref" ==
    field candidate "region_ref" &&
  field consumer "original_selected_antecedent_surface" == "Bush" &&
  spanIs (sub consumer "original_selected_antecedent_span") 4310 4314 &&
  field consumer "original_policy_ref" ==
    "slr:policy:source-local-repeated-person-topic:v1" &&
  field consumer "original_derivation_ref" ==
    field inference "derivation_ref" &&
  field consumer "original_review_item_ref" ==
    field inspection "review_item_ref" &&
  field consumer "original_s29_status" ==
    field inspection "s29_review_status" &&
  field consumer "answer_kind" ==
    "DERIVED_UNDER_NAMED_TOPIC_POLICY" &&
  yes inference "source_local_inference_derived" &&
  yes consumer "source_local_policy_inference_paid" &&
  decide (number inference "distinct_supporting_original_sentences" >= 2) &&
  support.size == (arr inference "supporting_person_mentions").size &&
  !(yes consumer "typed_unique_identity_witness_paid") &&
  !(yes consumer "governed_semantic_identity_paid") &&
  !(yes consumer "level_three_substitution_paid") &&
  !(yes consumer "external_qid_paid") &&
  !(yes consumer "historical_truth_paid") &&
  field replay "result" == "CURRENT" &&
  yes replay "previous_interpretation_usable" &&
  yes replay "original_level_one_source_preserved" &&
  !(yes replay "original_level_three_retracted_here") &&
  !(yes replay "external_identity_inferred") &&
  field replay "prior_receipt_ref" ==
    field consumer "answer_receipt_ref" &&
  field replayAnswer "answer_receipt_ref" ==
    field consumer "answer_receipt_ref" &&
  field replayAnswer "source_revision_ref" ==
    field consumer "source_revision_ref" &&
  field replayAnswer "answer_value" ==
    field consumer "answer_value"

/-- The exact source answer is one premise, not an inference from proximity
    or a declaration of all-world identity. -/
def checkConsumer
    (inspection frontier inference consumer replay : Json) : Bool :=
  decide (field consumer "answer_value" = "Bush") &&
  coherentSource inspection frontier inference consumer replay

structure CheckedConsumer
    (inspection frontier inference consumer replay : Json) where
  check : checkConsumer inspection frontier inference consumer replay = true

theorem checked_consumer_yields_source_local_bush
    {inspection frontier inference consumer replay : Json}
    (w : CheckedConsumer inspection frontier inference consumer replay) :
    field consumer "answer_value" = "Bush" := by
  have h := (Bool.and_eq_true.mp w.check).1
  exact of_decide_true h

theorem q207_cannot_be_q23505 :
    ("Q207" : String) ≠ "Q23505" := by decide

end Wikidata.Slr.GwbSourceLocalConsumer

def main (args : List String) : IO UInt32 := do
  match args with
  | [inspectionPath,frontierPath,inferencePath,consumerPath,replayPath] =>
    let i ← IO.FS.readFile inspectionPath
    let f ← IO.FS.readFile frontierPath
    let n ← IO.FS.readFile inferencePath
    let c ← IO.FS.readFile consumerPath
    let r ← IO.FS.readFile replayPath
    match Json.parse i, Json.parse f, Json.parse n, Json.parse c, Json.parse r with
    | .ok inspection, .ok frontier, .ok inference,
      .ok consumer, .ok replay =>
      if h : Wikidata.Slr.GwbSourceLocalConsumer.checkConsumer
          inspection frontier inference consumer replay = true then
        let witness : Wikidata.Slr.GwbSourceLocalConsumer.CheckedConsumer
            inspection frontier inference consumer replay := ⟨h⟩
        let _ := Wikidata.Slr.GwbSourceLocalConsumer.checked_consumer_yields_source_local_bush
          witness
        IO.println "GWB_SOURCE_LOCAL_CONSUMER_KERNEL_OK"
        IO.println "Current source-relative Bush answer, independent of governed identity/QID/truth"
        return 0
      else
        IO.eprintln "GWB_SOURCE_LOCAL_CONSUMER_REJECTED: source/policy/replay mismatch"
        return 1
    | _,_,_,_,_ =>
      IO.eprintln "GWB_SOURCE_LOCAL_CONSUMER_REJECTED: malformed original input"
      return 1
  | _ =>
    IO.eprintln "usage: lake env lean --run GwbSourceLocalConsumer.lean INSPECT FRONTIER INFERENCE CONSUMER REPLAY"
    return 2

#print axioms Wikidata.Slr.GwbSourceLocalConsumer.checked_consumer_yields_source_local_bush
#print axioms Wikidata.Slr.GwbSourceLocalConsumer.q207_cannot_be_q23505
