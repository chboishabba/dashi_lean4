#!/usr/bin/env python3
"""Original SensibLaw typed-binding ↔ original SLR source-coordinate weld.

Runs SensibLaw's own compact_binding_artifacts on its *real* preserved
PNF+annotation graph. NO duplicated binder, rerun parser, auto coreference,
candidate promotion, cross-work guess or QID attachment.

The original native book canonical text must hash to the exact SLR source,
and original SLR document_ref must exactly match that PNF graph.
Only factor anchors whose parser tokens reconstruct exact character
intervals enter the crosswalk.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import sys
from pathlib import Path
from typing import Any

from tools.gwb_native_maxcut_ledger import (
    BOOK_SHA, EvidenceRejected, bounded_span, require, validate_frontier,
    validate_inspection, write_json,
)


def factor_anchor_spans(artifacts: dict[str, Any], compiled: dict[str, Any],
                        document: str) -> dict[str, dict[str, Any]]:
    layer = artifacts.get("semantic_annotation_layer")
    require(isinstance(layer, dict), "no original semantic annotation graph")
    spans = layer.get("span_annotations")
    require(isinstance(spans, list), "no original parser token graph")
    by_start: dict[int, int] = {}
    by_end: dict[int, int] = {}
    for s in spans:
        if not isinstance(s, dict) or s.get("annotation_type") != "parser_token":
            continue
        value = s.get("value")
        if not isinstance(value, dict):
            continue
        ts, te = s.get("start_token"), s.get("end_token")
        st, en = value.get("start_char"), value.get("end_char")
        require(all(type(x) is int for x in (ts, te, st, en)) and
                0 <= ts < te and 0 <= st < en,
                "invalid original parser token coordinates")
        require(ts not in by_start or by_start[ts] == st,
                "original factor start-token collision")
        require(te not in by_end or by_end[te] == en,
                "original factor end-token collision")
        by_start[ts], by_end[te] = st, en
    require(bool(by_start), "no original parser token offset map")
    text = artifacts["canonical_text"]
    anchors: dict[str, dict[str, Any]] = {}
    for a in compiled.get("factor_anchors") or []:
        ref = a.get("factor_ref")
        ts, te = a.get("start_token"), a.get("end_token")
        require(isinstance(ref, str) and bool(ref) and
                type(ts) is int and type(te) is int and
                a.get("document_ref") == document,
                "foreign original factor-anchor coordinate")
        if ts not in by_start or te not in by_end:
            continue
        st, en = by_start[ts], by_end[te]
        require(0 <= st < en <= len(text), "original factor outside full source")
        require(ref not in anchors or (
            anchors[ref]["start_char"] == st and
            anchors[ref]["end_char"] == en
        ), "factor ref reused with conflicting original positions")
        anchors[ref] = {
            "factor_ref":ref,
            "factor_revision_ref":a["factor_revision_ref"],
            "document_ref":document,
            "start_char":st,"end_char":en,
            "surface":text[st:en],
            "parser_pos":a.get("parser_pos"),
            "parser_dependency":a.get("parser_dependency"),
            "morphology":a.get("morphology"),
            "quotation_depth":a.get("quotation_depth"),
            "referential_type_ref":a.get("pnf_kind_ref"),
        }
    return anchors


def weld_original_binding(
    inspection: dict[str, Any], frontier: dict[str, Any],
    artifacts: dict[str, Any], compiled: dict[str, Any]
) -> dict[str, Any]:
    original_sentences = validate_inspection(inspection)
    native_nominations = validate_frontier(
        inspection, frontier, original_sentences)
    canonical_text = artifacts.get("canonical_text")
    require(isinstance(canonical_text, str) and
            hashlib.sha256(canonical_text.encode("utf-8")).hexdigest() == BOOK_SHA,
            "original SensibLaw artifact text is not the exact native SLR book")
    graph = artifacts.get("pnf_graph")
    require(isinstance(graph, dict) and
            graph.get("document_ref") == inspection["document_ref"],
            "original PNF graph document identity does not match SLR")
    summary = compiled.get("binding_compaction_summary")
    require(isinstance(summary, dict) and
            summary.get("generation_mode") == "direct_observation_graph_index"
            and summary.get("authority") == "diagnostic_only",
            "original typed binder was not direct observation-graph mode")
    require(compiled.get("binding_accessibility_declaration",{}).get(
                "authority") == "configuration_only" and
            compiled.get("binding_compatibility_declaration",{}).get(
                "authority") == "configuration_only",
            "original binder structural declarations have been promoted")
    anchors = factor_anchor_spans(artifacts,compiled,inspection["document_ref"])
    focus_candidates = sorted(
        (a for a in anchors.values() if
         a["start_char"] == 4534 and a["end_char"] == 4536 and
         a["surface"] == "he"),
        key=lambda a:a["factor_ref"]
    )
    require(bool(focus_candidates), "original typed binder lacks exact focus factor")
    native_spans = {
        (n["original_start_char"], n["original_end_char"], n["surface"])
        for n in native_nominations
    }
    by_factor = {x["factor_ref"]:x for x in anchors.values()}
    matched_sets = []
    omitted_by_cap = 0
    for b in compiled.get("binding_candidate_sets") or []:
        require(b.get("schema_version") == "sl.binding_candidate_set.v0_2",
                "not the original typed binder set")
        if b.get("reference_factor_ref") not in {
            a["factor_ref"] for a in focus_candidates
        }:
            continue
        members = []
        for m in b.get("members") or []:
            ref = m.get("candidate_factor_ref")
            require(isinstance(ref, str) and bool(ref),
                    "binder candidate factor has no identity")
            anchor = by_factor.get(ref)
            require(anchor is not None, "binder candidate has no original exact-span anchor")
            require(anchor["end_char"] <= 4534,
                    "binder candidate is not before original pronoun")
            members.append({
                "factor_ref":ref,
                "original_source_anchor":anchor,
                "present_in_native_five_region_frontier":
                    (anchor["start_char"],anchor["end_char"],
                     anchor["surface"]) in native_spans,
                "accessibility_path_ref":m.get("accessibility_path_ref"),
                "compatibility_state":m.get("compatibility_state"),
                "compatibility_assessment_ref":
                    m.get("compatibility_assessment_ref"),
                "independent_identity_admission_paid":False
            })
        for exclusion in b.get("exclusion_summaries") or []:
            if exclusion.get("reason_ref") == "candidate_limit_truncation":
                count = exclusion.get("excluded_count")
                require(type(count) is int and count >= 0,
                        "original binder truncation count invalid")
                omitted_by_cap += count
        matched_sets.append({
            "candidate_set_ref":b.get("candidate_set_ref"),
            "reference_factor_ref":b["reference_factor_ref"],
            "reference_factor_revision_ref":b.get("reference_factor_revision_ref"),
            "accessibility_declaration_ref":b.get("accessibility_declaration_ref"),
            "compatibility_declaration_ref":b.get("compatibility_declaration_ref"),
            "referential_type_ref":b.get("referential_type_ref"),
            "original_binder_member_count":len(members),
            "members":members,
            "original_binder_exclusion_summaries":
                b.get("exclusion_summaries") or [],
            "original_binder_residuals":b.get("residuals") or [],
            "original_typed_binding_authority":"candidate_only"
        })
    require(bool(matched_sets), "no original typed binding set for exact he factor")
    return {
        "schema":"gwb-original-sensiblaw-typed-binding-to-slr-v1",
        "authority":"SOURCE_EQUIVALENCE_AND_CANDIDATE_SET_ONLY",
        "book_document_ref":inspection["document_ref"],
        "book_source_revision_ref":inspection["source_revision_ref"],
        "canonical_content_sha256":BOOK_SHA,
        "original_binder_compaction_mode":"direct_observation_graph_index",
        "slr_parser_run_ref":frontier["parser_run_ref"],
        "s29_review_item_ref":inspection["review_item_ref"],
        "focus_original_char_span":[4534,4536],
        "source_factor_anchors_provenance_checked":len(anchors),
        "source_focus_factors":focus_candidates,
        "typed_candidate_sets":matched_sets,
        "original_binder_candidate_limit_truncation_count":omitted_by_cap,
        "requires_omitted_candidate_audit":omitted_by_cap > 0,
        "candidate_scope_exhaustive":False,
        "resolved_unique":False,
        "semantic_review_paid":False,
        "external_qid_paid":False,
        "claimed_same_work_or_qid_equivalence":False,
    }


def main() -> int:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--slr-inspection", type=Path, required=True)
    p.add_argument("--slr-frontier", type=Path, required=True)
    p.add_argument("--original-sensiblaw-artifacts", type=Path, required=True)
    p.add_argument("--sensiblaw-root", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args=p.parse_args()
    sys.path.insert(0,str(args.sensiblaw_root.resolve()))
    # Attribute this transformation to the ORIGINAL preserved producer.
    from src.pnf.binding_candidate_sets import compact_binding_artifacts
    inspection=json.loads(args.slr_inspection.read_text(encoding="utf-8"))
    frontier=json.loads(args.slr_frontier.read_text(encoding="utf-8"))
    artifacts=json.loads(args.original_sensiblaw_artifacts.read_text(
        encoding="utf-8"))
    compact=compact_binding_artifacts(artifacts)
    result=weld_original_binding(inspection,frontier,artifacts,compact)
    write_json(args.output,result)
    print("GWB_ORIGINAL_TYPED_BINDING_SOURCE_WELD_OK "
          f"typed_sets={len(result['typed_candidate_sets'])} "
          "identity=UNPAID qid=UNPAID")
    return 0


if __name__=="__main__":
    raise SystemExit(main())
