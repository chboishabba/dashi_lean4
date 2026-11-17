#!/usr/bin/env python3
"""P5–P10 exact-source evidence ledger. Audit only; never manufacture review.

Inputs are the PR #112 committed acceptance manifest and, optionally, original
SLR M12/S28 evidence, the DASHI Agda reviewed seed overlay, or independent
JMD world proof report. Outputs distinguish exact *checked* evidence from
candidate-only metadata. Passing an audit means the classification is sound,
NOT that all six research gates are satisfied.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

MANIFEST_SCHEMA = "gwb-committed-rust-lean-proof-v1"
OVERLAY_SCHEMA = "slr-gwb-reviewed-wikimedia-identities-v1"


def read(path: Path) -> dict:
    result = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(result, dict):
        raise ValueError(f"not a JSON object: {path}")
    return result


def audit_manifest(manifest: dict) -> dict[str, dict]:
    if manifest.get("schema") != MANIFEST_SCHEMA:
        raise ValueError("missing original GWB P4 committed manifest schema")
    if manifest.get("source_revision") != "enwiki-revid:1385850169":
        raise ValueError("incorrect GWB source revision")
    if manifest.get("lean_source_fibre_receipt") != "PASSED":
        raise ValueError("GWB native receipt not checked")
    return {
        "P5": {"state": "OPEN", "requires": "reviewed mention→referent at original sentence/span; topic QID is insufficient"},
        "P6": {"state": "OPEN", "requires": "original checked M12 literal and S28 event ancestry plus reviewed event-identity equivalence"},
        "P7": {"state": "OPEN", "requires": "reviewed event-scoped temporal interpretation (not candidate S28 chronology)"},
        "P8": {"state": "OPEN", "requires": "all-live semantic reading coverage and independent source→reading factorisation for identity/time query"},
        "P9": {"state": "OPEN", "requires": "reviewed article proposition ↔ independently imported JMD property equivalence"},
        "P10": {"state": "OPEN", "requires": "all original 51 QIDs reimported and every original edge JMD-supported; never world truth"},
    }


def audited_overlay(path: Path) -> dict:
    rows = []
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        row = json.loads(line)
        if row.get("schema") != OVERLAY_SCHEMA:
            raise ValueError("not the original reviewed Wikimedia seed overlay")
        if row.get("candidate_only") is not True or row.get("semantic_promotion") is not False:
            raise ValueError("seed overlay attempts semantic promotion")
        rows.append(row)
    if not rows:
        raise ValueError("empty reviewed seed overlay")
    return {
        "rows": len(rows),
        "topic_only": sum(str(row.get("identity_scope", "")).startswith("topic-anchor") for row in rows),
        "exact_source_work": sum(row.get("identity_scope") == "exact-work-identity" for row in rows),
        "semantic_actor_identity_admitted": False,
    }


def classify(manifest: dict, overlay: dict | None = None, s28: dict | None = None,
             world: dict | None = None) -> dict:
    result = audit_manifest(manifest)
    if overlay:
        result["P5"]["reviewed_topic_seed_overlay"] = overlay
        result["P5"]["reason"] = "reviewed topic/source-work QIDs are not GWB article span-level mention identity"
    if s28:
        if s28.get("schema") != "slr-s28-event-chronology-candidates-v1":
            raise ValueError("not original SLR S28 chronology candidates schema")
        if s28.get("candidate_only") is not True or s28.get("semantic_promotion") is not False:
            raise ValueError("S28 evidence attempts unreviewed promotion")
        if s28.get("event_occurrence_paid") is not False:
            raise ValueError("candidate S28 cannot claim world occurrence")
        result["P6"]["source_candidate_trace_seen"] = True
        result["P7"]["temporal_candidate_trace_seen"] = True
        result["P6"]["reason"] = "S28 ancestry is not a reviewed event-equivalence proof"
        result["P7"]["reason"] = "S28 temporal candidate is not a reviewed temporal-admission proof"
    if world:
        if world.get("article_semantic_alignment_paid") is not False:
            raise ValueError("JMD graph receipt cannot independently claim article semantic alignment")
        result["P9"]["independent_jmd_graph_receipt_seen"] = True
        result["P10"]["independent_jmd_graph_receipt_seen"] = True
        result["P9"]["reason"] = "KB property proof is not an article-proposition semantic alignment"
    return result


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--manifest", type=Path,
                   default=Path("artifacts/gwb-semantic-proof/proof_run_manifest.json"))
    p.add_argument("--overlay", type=Path)
    p.add_argument("--s28", type=Path)
    p.add_argument("--world", type=Path)
    p.add_argument("--output", type=Path)
    p.add_argument("--strict", action="store_true")
    args = p.parse_args()
    status = classify(
        read(args.manifest),
        audited_overlay(args.overlay) if args.overlay else None,
        read(args.s28) if args.s28 else None,
        read(args.world) if args.world else None,
    )
    result = {
        "schema": "gwb-p5-p10-gate-audit-v1",
        "source_revision": "enwiki-revid:1385850169",
        "source_manifest": str(args.manifest),
        "semantic_completion_claimed": False,
        "gates": status,
    }
    raw = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(raw, encoding="utf-8")
    else:
        print(raw, end="")
    if args.strict:
        print("GWB_P5_P10_STRICT_OPEN: original reviewed semantic obligations not paid")
        return 3
    print("GWB_P5_P10_EVIDENCE_CLASSIFIED: audit passed, semantic gates remain open")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
