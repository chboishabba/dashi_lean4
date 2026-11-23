#!/usr/bin/env python3
"""M1–M3: independent original-SLR book / Q207 JMD evidence ledger.

Input is *actual* native SLR C4.12 inspect JSON and M1 original-parser
frontier JSON, never a simulated identity result. This is not a parser,
coreference resolver, S29 review action, QID linker or truth judge.

Produces:
  - canonical source-bound joint audit
  - exact candidate-by-candidate review worksheet, with all decisions UNPAID
  - source-local unresolved consumer answer, backed by the observed frontier
  - separate Wikipedia Q207 lane, with no book -> Q207 cast
  - an explicit residual inventory and immutable input digests.

Strong positive local identity requires a future separately executed,
original-owner-governed antecedent resolution. This script cannot assert it.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

BOOK_SHA = "7ff2ec8ffe6243871ad682e7d7060fe3b84025fb15dbe229154d7aa7f6a72b30"
WIKI_SHA = "a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233"
REVIEW_ITEM = (
    "review-item:native-antecedent-candidate:sha256:"
    "25e927f12a0092fbed143669f6a0621fa004636d728074d576275b361da8f7d1"
)
LEAN_MARKER = "GWB_NATIVE_FRONTIER_BOUNDARY_KERNEL_OK"
Q207_MARKER = "GWB_Q207_MINIMAL_KERNEL_OK"


class EvidenceRejected(ValueError):
    """This exact source/ownership/authority assertion is not proved."""


def require(predicate: bool, label: str) -> None:
    if not predicate:
        raise EvidenceRejected(label)


def hash_json(value: Any) -> str:
    return hashlib.sha256(
        json.dumps(value, ensure_ascii=False, sort_keys=True,
                   separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def bounded_span(entry: dict[str, Any], a: int, b: int) -> str:
    start = entry.get("start_char")
    end = entry.get("end_char")
    literal = entry.get("literal")
    require(type(start) is int and type(end) is int and
            isinstance(literal, str) and 0 <= start < end and
            len(literal) == end - start, "original source statement invalid")
    require(type(a) is int and type(b) is int and
            start <= a < b <= end, "candidate outside original statement")
    return literal[a-start:b-start]


def validate_inspection(j: dict[str, Any]) -> list[dict[str, Any]]:
    require(j.get("schema") == "slr-native-antecedent-s29-inspection-v1",
            "not the original C4.12 inspection schema")
    require(j.get("review_item_ref") == REVIEW_ITEM,
            "wrong original S29 review item")
    require(j.get("canonical_content_sha256") == BOOK_SHA,
            "wrong book manifest/source digest")
    require(j.get("document_ref") == "document:sha256:" + BOOK_SHA,
            "book original document is not the pinned one")
    for field in ("original_source_ref", "source_revision_ref",
                  "original_context_sha256", "proposal_ref"):
        require(isinstance(j.get(field), str) and bool(j[field]),
                f"missing immutable provenance {field}")
    require(j.get("candidate_only") is True and
            j.get("identity_admission_paid") is False and
            j.get("external_qid_paid") is False and
            j.get("claim_truth_paid") is False,
            "C4.12 inspection unexpectedly promotes authority")
    require(j.get("antecedent_resolution") == "REVIEW_REQUIRED",
            "C4.12 identity gate changed")
    require(j.get("s29_review_status") in
            ("Pending", "Accepted", "Rejected", "NeedsEvidence",
             "Qualified", "Abstained", "Superseded"),
            "unrecognized original S29 workflow status")
    cmds = j.get("s29_receipt_commands")
    require(isinstance(cmds, list) and
            all(isinstance(x, str) and bool(x) for x in cmds) and
            len(set(cmds)) == len(cmds), "invalid S29 receipt command list")
    before = j.get("before")
    at = j.get("focus_statement")
    after = j.get("after")
    require(isinstance(before, list) and len(before) == 4 and
            isinstance(after, list) and len(after) == 2 and
            isinstance(at, dict), "expected exactly original sentences 19–25")
    entries = before + [at] + after
    ids: set[str] = set()
    previous_end = 0
    for s in entries:
        require(isinstance(s, dict), "corrupt SLR source sentence")
        for key in ("statement_ref", "region_ref"):
            require(isinstance(s.get(key), str) and bool(s[key]),
                    f"missing {key}")
        st, en = s.get("start_char"), s.get("end_char")
        require(type(st) is int and type(en) is int and
                st >= previous_end and en > st, "original sentence disorder")
        require(len(s.get("literal", "")) == en - st,
                "original sentence Unicode coordinates changed")
        require(s["statement_ref"] not in ids,
                "original SLR source statement duplicated")
        ids.add(s["statement_ref"])
        previous_end = en
    focus = j.get("focus")
    candidate = j.get("candidate_antecedent")
    require(isinstance(focus, dict) and isinstance(candidate, dict),
            "no C4.12 exact candidate and focus")
    require(focus.get("start_char") == 4534 and
            focus.get("end_char") == 4536 and
            focus.get("surface") == "he" and
            focus.get("statement_ref") == at["statement_ref"] and
            focus.get("region_ref") == at["region_ref"],
            "focus reference not the original book 'he'")
    require(bounded_span(at, 4534, 4536) == "he",
            "original source focus surface mismatch")
    require(candidate.get("start_char") == 4310 and
            candidate.get("end_char") == 4314 and
            candidate.get("surface") == "Bush",
            "candidate reference not the original Bush")
    matches = [
        s for s in before
        if s["statement_ref"] == candidate.get("statement_ref")
        and s["region_ref"] == candidate.get("region_ref")
    ]
    require(len(matches) == 1 and
            bounded_span(matches[0], 4310, 4314) == "Bush",
            "exact original Bush source span missing")
    return entries


def validate_frontier(
    inspection: dict[str, Any], f: dict[str, Any],
    entries: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    require(f.get("schema") == "slr-native-antecedent-bounded-frontier-v1",
            "not SLR original parser nomination frontier")
    for field in ("original_source_ref", "source_revision_ref", "document_ref",
                  "canonical_content_sha256", "review_item_ref",
                  "s29_review_status"):
        require(f.get(field) == inspection.get(field),
                f"frontier and C4.12 do not share original {field}")
    require(f.get("focus_mention_ref") == inspection["focus"]["mention_ref"] and
            f.get("focus_start_char") == 4534 and
            f.get("focus_end_char") == 4536 and
            f.get("focus_surface") == "he",
            "frontier focus identity/coordinates mismatch")
    require(f.get("nominated_source_anchor_ref") ==
            inspection["candidate_antecedent"]["statement_ref"] and
            f.get("nominated_source_anchor_start_char") == 4310 and
            f.get("nominated_source_anchor_end_char") == 4314,
            "selected original source candidate changed")
    require(isinstance(f.get("parser_run_ref"), str) and
            bool(f["parser_run_ref"]), "missing original parser-run reference")
    require(isinstance(f.get("candidate_set_ref"), str) and
            f["candidate_set_ref"].startswith(
                "native-antecedent-bounded-frontier:sha256:"),
            "not a native source-derived candidate set")
    require(f.get("structural_region_coverage_complete") is True and
            f.get("original_regions_covered") == 5,
            "incomplete original parser-source observations")
    require(f.get("semantic_candidate_exhaustiveness_paid") is False and
            f.get("local_antecedent_admission_paid") is False and
            f.get("external_qid_paid") is False and
            f.get("claim_truth_paid") is False and
            f.get("source_relative_answer") == "UNRESOLVED_REVIEW_REQUIRED",
            "unpaid identity or world authority forged")
    nominations = f.get("nominations")
    require(isinstance(nominations, list) and
            nominations and len(nominations) == f.get("parser_nomination_count"),
            "empty or inconsistent native nominations")
    references = {}
    for s in entries[:5]:
        references[(s["statement_ref"], s["region_ref"])] = s
    seen: set[str] = set()
    has_bush = False
    for n in nominations:
        require(isinstance(n, dict), "invalid nomination")
        ref = n.get("nomination_ref")
        require(isinstance(ref, str) and
                ref.startswith("native-parser-nomination:sha256:") and
                ref not in seen, "missing/duplicate original parser nomination")
        seen.add(ref)
        k = (n.get("original_statement_ref"),
             n.get("original_region_ref"))
        require(k in references, "foreign or following-sentence source nomination")
        a, b = n.get("original_start_char"), n.get("original_end_char")
        require(n.get("surface") == bounded_span(references[k], a, b),
                "nomination does not match original source string/Unicode interval")
        require(b <= 4534 and n.get("in_preceding_source") is True and
                n.get("source_verified") is True and
                n.get("semantic_admission_paid") is False,
                "future or promoted nomination")
        require(n.get("observation_kind") in ("parser_token", "parser_entity"),
                "not an original persisted parser observation")
        require(isinstance(n.get("parser_compilation_key"), str) and
                bool(n["parser_compilation_key"]) and
                isinstance(n.get("parser_observation_ref"), str) and
                bool(n["parser_observation_ref"]),
                "missing original native parser provenance")
        require(n.get("morphological_resolution") == "UNASSESSED" and
                n.get("quotation_scope") == "UNASSESSED",
                "typed binding/quotation judgement was fabricated")
        if (a, b, n.get("surface"), n.get("original_statement_ref")) == (
                4310, 4314, "Bush",
                inspection["candidate_antecedent"]["statement_ref"]):
            has_bush = True
    require(has_bush, "original Bush nomination absent from parser frontier")
    return nominations


def make_ledger(inspection: dict[str, Any], frontier: dict[str, Any],
                *, lean_log: str = "",
                q207_log: str = "") -> tuple[dict[str, Any], dict[str, Any]]:
    entries = validate_inspection(inspection)
    nominations = validate_frontier(inspection, frontier, entries)
    if lean_log:
        require(LEAN_MARKER in lean_log,
                "Lean kernel did not emit bounded frontier marker")
    if q207_log:
        require(Q207_MARKER in q207_log,
                "JMD Q207 minimal source-field kernel marker absent")
    reviews = [
        {
            "nomination_ref": n["nomination_ref"],
            "original_statement_ref": n["original_statement_ref"],
            "region_ref": n["original_region_ref"],
            "source_span": [n["original_start_char"], n["original_end_char"]],
            "literal_surface": n["surface"],
            "parser_observation_ref": n["parser_observation_ref"],
            "parser_pos_or_label": n["parser_pos_or_label"],
            "morphology": n["parser_morph_json"],
            "accessibility_witness_ref": None,
            "morphology_compatibility": "UNASSESSED",
            "quotation_scope": "UNASSESSED",
            "reviewer_disposition": "UNREVIEWED",
            "exclusion_witness_refs": [],
        }
        for n in nominations
    ]
    worksheet = {
        "schema": "slr-original-book-antecedent-review-worksheet-v1",
        "authority": "REVIEW_PREPARATION_ONLY",
        "source_revision_ref": inspection["source_revision_ref"],
        "document_ref": inspection["document_ref"],
        "review_item_ref": inspection["review_item_ref"],
        "candidate_set_ref": frontier["candidate_set_ref"],
        "focus": inspection["focus"],
        "selected_C410_nomination": inspection["candidate_antecedent"],
        "candidate_count_bounded_parser_observations": len(reviews),
        "semantic_fibre_exhaustiveness": "NOT_PROVEN",
        "reviewer_ref": None,
        "s29_accepted_command_ref": None,
        "typed_resolution_policy_ref": None,
        "semantic_resolution_receipt_ref": None,
        "nominees": reviews,
        "review_complete": False,
        "identity_admission_paid": False,
        "external_qid_paid": False,
    }
    residuals = [
        "M1: full semantic accessibility / syntactic binding and quotation scope",
        "M1: reviewed rival exclusions and independently admitted local antecedent witness",
        "M1: reversible Level-3 local identity substitution with original owner",
        "M2: live-reading consumer coverage or independent invariance certificate",
        "M2: independently pinned book actor Q23505 world-authority witness",
        "M3: independently reviewed Q207 Wikipedia article-property alignment",
        "M3: JMD kernel-checked property/KB proof, exact demand and payment",
        "C6: dependent selective reopening after a real evidence change",
    ]
    book = {
        "source_kind": "original_book_text_not_wikipedia_article",
        "source_revision_ref": inspection["source_revision_ref"],
        "canonical_content_sha256": BOOK_SHA,
        "document_ref": inspection["document_ref"],
        "original_review_item_ref": inspection["review_item_ref"],
        "s29_workflow_status": inspection["s29_review_status"],
        "candidate_set_ref": frontier["candidate_set_ref"],
        "parser_run_ref": frontier["parser_run_ref"],
        "question": "To whom does 'he' in original book sentence 23 refer?",
        "focus": inspection["focus"],
        "nominated_source_span": inspection["candidate_antecedent"],
        "bounded_parser_nomination_count": len(nominations),
        "bounded_parser_source_regions": 5,
        "semantic_exhaustiveness_paid": False,
        "answer_kind": "EXPLICIT_UNRESOLVED",
        "answer_value": None,
        "possible_antecedent_surface": "Bush",
        "source_relative_identity_paid": False,
        "world_q23505_paid": False,
        "world_q207_book_attachment_paid": False,
        "claim_truth_paid": False,
        "original_s29_receipt_count": len(inspection["s29_receipt_commands"]),
        "lean_bounded_frontier_boundary_checked": bool(lean_log),
    }
    wiki = {
        "source_kind": "pinned_wikipedia_george_w_bush_article",
        "source_revision_ref": "enwiki-revid:1385850169",
        "canonical_content_sha256": WIKI_SHA,
        "root_qid": "Q207",
        "minimum_source_field_kernel_checked_in_this_packet": bool(q207_log),
        "article_semantic_relation_to_book": "NOT_ESTABLISHED",
        "book_local_identity_from_Q207": False,
        "independently_reviewed_article_kb_property_paid": False,
        "complete_51_qid_world_proof_paid": False,
    }
    ledger = {
        "schema": "gwb-native-m1-m3-joint-maxcut-ledger-v1",
        "authority": "EVIDENCE_INVENTORY_WITH_EXPLICIT_UNPAID_GATES",
        "input_inspection_sha256": hash_json(inspection),
        "input_frontier_sha256": hash_json(frontier),
        "source_revision_scopes_distinct": BOOK_SHA != WIKI_SHA,
        "book_lane": book,
        "wikipedia_lane": wiki,
        "externally_reviewed_book_to_wikipedia_alignment_paid": False,
        "consumer_scope_global_completeness_paid": False,
        "open_obligations": residuals,
        "complete_semantic_system": False,
    }
    return ledger, worksheet


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(value, indent=2, ensure_ascii=False, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--inspection", type=Path, required=True)
    p.add_argument("--frontier", type=Path, required=True)
    p.add_argument("--lean-log", type=Path)
    p.add_argument("--q207-log", type=Path)
    p.add_argument("--ledger", type=Path, required=True)
    p.add_argument("--worksheet", type=Path, required=True)
    args = p.parse_args()
    inspection = json.loads(args.inspection.read_text(encoding="utf-8"))
    frontier = json.loads(args.frontier.read_text(encoding="utf-8"))
    log = args.lean_log.read_text(encoding="utf-8") if args.lean_log else ""
    q207log = args.q207_log.read_text(encoding="utf-8") if args.q207_log else ""
    ledger, worksheet = make_ledger(
        inspection, frontier, lean_log=log, q207_log=q207log
    )
    write_json(args.ledger, ledger)
    write_json(args.worksheet, worksheet)
    print(
        "GWB_NATIVE_MAXCUT_LEDGER_OK "
        f"parser_nominations={worksheet['candidate_count_bounded_parser_observations']} "
        "local_identity=UNPAID external_qid=UNPAID claim_truth=UNPAID "
        f"lean_frontier_boundary={'CHECKED' if log else 'UNTESTED'}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
