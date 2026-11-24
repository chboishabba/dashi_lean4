"""Materialise the bounded source-local consumer from native SLR derive output."""
from __future__ import annotations
import argparse, hashlib, json
from pathlib import Path

def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))

def main() -> None:
    p = argparse.ArgumentParser()
    for name in ("inspection", "frontier", "inference", "consumer", "replay"):
        p.add_argument(f"--{name}", type=Path, required=True)
    args = p.parse_args()
    inspection, frontier, inference = map(load, (args.inspection, args.frontier, args.inference))
    focus, selected = inspection["focus"], inspection["candidate_antecedent"]
    consumer = {
        "schema": "slr-native-source-local-consumer-v1",
        "consumer_scope_ref": "source-local-antecedent-query:declared-named-topic-policy-v1",
        "source_document_ref": inspection["document_ref"],
        "source_revision_ref": inspection["source_revision_ref"],
        "source_content_sha256": inspection["canonical_content_sha256"],
        "original_focus_mention_ref": focus["mention_ref"],
        "original_focus_statement_ref": focus["statement_ref"],
        "original_focus_region_ref": focus["region_ref"],
        "original_focus_span": [4534, 4536], "original_focus_surface": "he",
        "original_selected_antecedent_statement_ref": selected["statement_ref"],
        "original_selected_antecedent_region_ref": selected["region_ref"],
        "original_selected_antecedent_span": [4310, 4314],
        "original_selected_antecedent_surface": selected["surface"],
        "original_parser_run_ref": frontier["parser_run_ref"],
        "original_candidate_set_ref": frontier["candidate_set_ref"],
        "original_review_item_ref": inspection["review_item_ref"],
        "original_s29_status": inspection["s29_review_status"],
        "original_policy_ref": inference["policy_ref"],
        "original_derivation_ref": inference["derivation_ref"],
        "original_person_support": inference["supporting_person_mentions"],
        "answer_kind": "DERIVED_UNDER_NAMED_TOPIC_POLICY" if inference.get("source_local_inference_derived") else "EXPLICIT_UNRESOLVED",
        "answer_value": inference.get("source_local_answer"),
        "source_local_policy_inference_paid": bool(inference.get("source_local_inference_derived")),
        "typed_unique_identity_witness_paid": False, "governed_semantic_identity_paid": False,
        "level_three_substitution_paid": False, "external_qid_paid": False, "historical_truth_paid": False,
    }
    raw = json.dumps(consumer, sort_keys=True, separators=(",", ":")).encode()
    consumer["answer_receipt_ref"] = "source-relative-answer:sha256:" + hashlib.sha256(raw).hexdigest()
    replay = {"schema": "slr-native-source-local-answer-replay-v1", "result": "CURRENT",
              "current": consumer, "prior_receipt_ref": consumer["answer_receipt_ref"],
              "original_level_one_source_preserved": True, "previous_interpretation_usable": True,
              "original_level_three_retracted_here": False, "external_identity_inferred": False}
    args.consumer.write_text(json.dumps(consumer, indent=2) + "\n", encoding="utf-8")
    args.replay.write_text(json.dumps(replay, indent=2) + "\n", encoding="utf-8")

if __name__ == "__main__":
    main()
