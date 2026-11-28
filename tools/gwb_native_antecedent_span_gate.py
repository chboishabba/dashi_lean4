#!/usr/bin/env python3
"""Exact same-source antecedent *candidate* geometry; never semantic admission.

Consumes the original SLR context receipt and an explicitly selected antecedent
source span. The reviewer selects the candidate; this only proves its exact
text/coordinate correspondence. No actor guessing, identity resolution, QID
join, database mutation or new parser.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any


class CoordinateReject(ValueError):
    """An exact source-coordinate or non-promotion invariant failed."""


def require(check: bool, reason: str) -> None:
    if not check:
        raise CoordinateReject(reason)


def canonical_digest(obj: Any) -> str:
    return hashlib.sha256(json.dumps(obj, ensure_ascii=False, sort_keys=True,
                                     separators=(",", ":")).encode("utf-8")).hexdigest()


def validated_entries(context: dict) -> tuple[list[dict], dict, dict, list[dict]]:
    require(context.get("schema") == "slr-native-original-discourse-context-v1",
            "not original SLR discourse context")
    require(context.get("antecedent_resolution") == "UNRESOLVED_REVIEW_REQUIRED"
            and context.get("resolved_referent") is None
            and context.get("semantic_authority_promoted") is False
            and context.get("external_qid") == "NOT_TESTED",
            "unresolved provenance boundaries changed")
    for k in ("original_source_ref", "source_revision_ref", "document_ref",
              "canonical_content_sha256"):
        require(isinstance(context.get(k), str) and bool(context[k]),
                f"missing source coordinate: {k}")
    sha = context["canonical_content_sha256"]
    require(len(sha) == 64 and all(x in "0123456789abcdef" for x in sha),
            "invalid content digest")
    require(context["document_ref"] == "document:sha256:" + sha,
            "canonical source/document mismatch")
    before, at, after = context.get("before"), context.get("at"), context.get("after")
    require(isinstance(before, list) and isinstance(at, dict)
            and isinstance(after, list), "missing original context entries")
    require(len(before) <= 20 and len(after) <= 20, "unexpected context window")
    entries = before + [at] + after
    ids: set[str] = set()
    for entry in entries:
        require(isinstance(entry, dict), "bad original context entry")
        for field in ("region_ref", "statement_ref", "literal"):
            require(isinstance(entry.get(field), str) and bool(entry[field]),
                    f"missing {field}")
        a, b = entry.get("start_char"), entry.get("end_char")
        require(type(a) is int and type(b) is int and 0 <= a < b,
                "invalid source character boundaries")
        require(len(entry["literal"]) == b - a,
                "original literal character length mismatch")
        require(entry.get("candidate_only") is True,
                "original context entry promoted")
        require(entry["statement_ref"] not in ids,
                "duplicate source statement")
        ids.add(entry["statement_ref"])
    for left, right in zip(entries, entries[1:]):
        require(left["end_char"] <= right["start_char"],
                "unordered or overlapping source statements")
    focus = context.get("focus")
    require(isinstance(focus, dict), "missing native focus")
    for field in ("mention_ref", "candidate_ref", "statement_ref", "region_ref", "surface"):
        require(isinstance(focus.get(field), str) and bool(focus[field]),
                f"missing focus {field}")
    require(focus["statement_ref"] == at["statement_ref"]
            and focus["region_ref"] == at["region_ref"],
            "focus not original at-statement")
    fa, fb = focus.get("start_char"), focus.get("end_char")
    require(type(fa) is int and type(fb) is int
            and at["start_char"] <= fa < fb <= at["end_char"],
            "focus outside original source")
    require(at["literal"][fa-at["start_char"]:fb-at["start_char"]] == focus["surface"],
            "focus original-surface mismatch")
    return before, at, focus, after


def check_candidate(context: dict, candidate: dict) -> dict:
    before, at, focus, _ = validated_entries(context)
    require(isinstance(candidate, dict),
            "candidate must be a source coordinate object")
    for field in ("statement_ref", "region_ref", "surface"):
        require(isinstance(candidate.get(field), str) and bool(candidate[field]),
                f"candidate missing {field}")
    a, b = candidate.get("start_char"), candidate.get("end_char")
    require(type(a) is int and type(b) is int and 0 <= a < b,
            "candidate invalid coordinate range")
    choices = [e for e in before + [at]
               if e["statement_ref"] == candidate["statement_ref"]
               and e["region_ref"] == candidate["region_ref"]]
    require(len(choices) == 1,
            "candidate not in original preceding discourse")
    chosen = choices[0]
    require(chosen["start_char"] <= a < b <= chosen["end_char"],
            "candidate outside selected source statement")
    require(chosen["literal"][a-chosen["start_char"]:b-chosen["start_char"]]
            == candidate["surface"], "candidate exact surface mismatch")
    require(b <= focus["start_char"], "candidate is not before the pronoun")
    require(not (a == focus["start_char"] and b == focus["end_char"]),
            "candidate cannot equal focus mention")
    return {
        "schema": "slr-native-antecedent-source-span-candidate-v1",
        "original_context_sha256": canonical_digest(context),
        "original_source_ref": context["original_source_ref"],
        "source_revision_ref": context["source_revision_ref"],
        "document_ref": context["document_ref"],
        "canonical_content_sha256": context["canonical_content_sha256"],
        "focus": dict(focus),
        "antecedent_source_span": {
            "statement_ref": chosen["statement_ref"],
            "region_ref": chosen["region_ref"],
            "start_char": a, "end_char": b, "surface": candidate["surface"],
        },
        "candidate_only": True,
        "same_source_span_geometry_checked": True,
        "antecedent_resolution": "REVIEW_REQUIRED",
        "identity_admission": "NOT_PAID",
        "external_qid": "NOT_TESTED",
        "claim_truth_paid": False,
        "semantic_authority_promoted": False,
        "review_owner": "SLR_GOVERNED_ANTECEDENT_REVIEW",
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--context", type=Path, required=True)
    p.add_argument("--candidate", type=Path, required=True)
    p.add_argument("--output", type=Path, required=True)
    args = p.parse_args()
    context = json.loads(args.context.read_text(encoding="utf-8"))
    candidate = json.loads(args.candidate.read_text(encoding="utf-8"))
    receipt = check_candidate(context, candidate)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2, ensure_ascii=False) + "\n",
                           encoding="utf-8")
    print("GWB_NATIVE_ANTECEDENT_SOURCE_SPAN_CHECKED identity=REVIEW_REQUIRED")


if __name__ == "__main__":
    main()
