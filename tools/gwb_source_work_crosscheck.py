#!/usr/bin/env python3
"""Recheck independent GWB source-*work* match (never antecedent identity).

The native SLR source and the SensibLaw timeline are separate manifests.
A whitespace-folded excerpt match is useful source attribution, not a
byte-identical manifestation, source revision or external QID witness.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
from tools.gwb_native_binding_adapter import require, sha


def git_blob_sha(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def folded(text: str) -> str:
    return " ".join(text.split())


def verify(native: dict, timeline: dict, receipt: dict, raw_timeline: bytes) -> dict:
    source, mention = native["source"], native["focus_mention"]
    r, t = receipt["native"], receipt["independent_timeline"]
    require(receipt.get("authority") == "candidate_only",
            "unreviewed work candidate promoted")
    require(native.get("authority") == "candidate_only"
            and not native.get("semantic_authority_promoted", True),
            "native candidate promoted")
    require(sha(source["document_literal"]) == source["region_literal_sha256"],
            "native region digest mismatch")
    for key in ("source_revision_ref", "document_ref", "statement_ref", "region_ref"):
        require(r[key] == source[key], "native source mismatch " + key)
    for key, focus_key in (
        ("focus_mention_ref", "mention_ref"),
        ("focus_start_char", "source_start_char"),
        ("focus_end_char", "source_end_char"),
    ):
        require(r[key] == mention[focus_key], "focus mismatch " + key)
    a, b = mention["source_start_char"], mention["source_end_char"]
    start = source["region_start_char"]
    require(source["document_literal"][a-start:b-start] == mention["surface"] == "he",
            "focus is not the original he span")
    require(git_blob_sha(raw_timeline) == t["git_blob_sha1"],
            "independent timeline Git blob mismatch")
    events = timeline.get("events") or []
    found = {e.get("event_id"): e for e in events
             if e.get("event_id") in (t["matching_event_id"],
                                     t["prior_same_work_event_id"])}
    require(len(found) == 2, "missing independent timeline events")
    current, previous = (found[t[key]] for key in
                         ("matching_event_id", "prior_same_work_event_id"))
    require(previous.get("path") == current.get("path") ==
            t["source_path_original"], "not an original same-work neighbor")
    native_excerpt = folded(source["document_literal"])
    event_excerpt = folded(current.get("text") or "")
    require(event_excerpt.startswith(native_excerpt),
            "independent source-work excerpt mismatch")
    require(len(native_excerpt) == receipt["comparison"]["native_folded_length"],
            "excerpt length differs from stored check")
    require("Bush" in (previous.get("text") or ""),
            "preceding same-work reference not present")
    require(t["shared_source_path"] is True,
            "invalid independent source-work receipt")
    status = receipt["comparison"]
    require(status.get("exact_native_manifestation_equality") == "NOT_PROVED"
            and status.get("reviewed_antecedent") == "NOT_PROVED"
            and status.get("external_person_qid") == "NOT_PROVED"
            and status.get("world_truth_promoted") is False,
            "independent work match illegally promoted to identity")
    return {"schema":"gwb-source-work-crosscheck-result-v1",
            "source_work_candidate":"MATCHED_INDEPENDENT_EXCERPT",
            "native_source_revision_ref":source["source_revision_ref"],
            "independent_timeline_blob_sha":t["git_blob_sha1"],
            "preceding_event_id":t["prior_same_work_event_id"],
            "matching_event_id":t["matching_event_id"],
            "native_char_start":a,"native_char_end":b,
            "identity_admission":"NOT_TESTED",
            "canonical_source_equality":"NOT_PROVED",
            "external_qid":"NOT_TESTED",
            "semantic_authority_promoted":False}


def main() -> None:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--native",type=Path,required=True)
    p.add_argument("--timeline",type=Path,required=True)
    p.add_argument("--crosscheck",type=Path,required=True)
    p.add_argument("--output",type=Path,required=True)
    args=p.parse_args()
    n=json.loads(args.native.read_text(encoding="utf-8"))
    raw=args.timeline.read_bytes()
    timeline=json.loads(raw.decode("utf-8"))
    receipt=json.loads(args.crosscheck.read_text(encoding="utf-8"))
    result=verify(n,timeline,receipt,raw)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print("GWB_NATIVE_SOURCE_WORK_EXCERPT_MATCHED",
          "admitted_identity=NOT_TESTED")


if __name__=="__main__": main()
