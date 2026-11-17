#!/usr/bin/env python3
"""Exact GWB unsupported-dependency audit, against the ORIGINAL SLR parser.

This is a *diagnostic projection* of the native Rust receipt. It does not
re-parse the text, reimplement SLR/ITIR, produce semantic alternatives, or
admit actor/event/time identities.

The 643-row receipt alone retains only token ordinals and residual kinds.
To recover the actual spaCy labels for all 12,543 unsupported tokens, the
same revision's ignored original .dashi/gwb-source/slr-record.json is REQUIRED.

In-repo owners:
- DASHI/Cognition/PNF/SensibLawGWBv01UnsupportedResidualCertificationV04Exact.agda
- DASHI/Cognition/PNF/SensibLawUnsupportedDemandRoutingExact.agda
- DASHI/Cognition/PNF/SensibLawUnsupportedResidualRelativeFibreExact.agda
- SensibLaw/src/language/semantic_reductions.py
- SensibLaw/src/language/graph.py
- SensibLaw/src/pnf/binding_candidate_sets.py

The v0.4 taxonomy was certified on the DIFFERENT 41,044-sentence GWB
tranche. This script reports labels not covered by that historical taxonomy
without pretending to change its exact measured counts.
"""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import json
from pathlib import Path

# Transcribed exact ROUTE clauses from the original Agda v0.4 routing owner.
V04_ROUTES = {
    "surfaceStructural": {"punct", "det", "predet", "intj", "meta"},
    "relationAttachment": {"prep", "pobj", "pcomp", "agent", "dative", "case", "prt"},
    "nominalStructure": {"compound", "poss", "nummod", "quantmod"},
    "predicateAction": {"ROOT", "attr", "acomp", "oprd", "csubj", "csubjpass", "expl", "parataxis"},
    "coordination": {"conj", "cc", "preconj"},
    "parserUnknown": {"dep"},
}
ROUTE = {label: route for route, labels in V04_ROUTES.items() for label in labels}
if len(ROUTE) != sum(map(len, V04_ROUTES.values())):
    raise RuntimeError("duplicated original v0.4 dependency label route")

EXPECTED_SOURCE_REV = "enwiki-revid:1385850169"
EXPECTED_SOURCE_HASH = "a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233"


def _array(obj, key):
    rows = obj.get(key)
    if not isinstance(rows, list):
        raise ValueError(f"expected list: {key}")
    return rows


def _original_sentence_map(slr):
    source = _array(slr, "pnf_candidates")
    out = {}
    for sentence in source:
        idx = sentence.get("sentence_index")
        if not isinstance(idx, int) or idx in out:
            raise ValueError(f"missing/duplicate original sentence index {idx}")
        out[idx] = _array(sentence, "dependency_rows")
    return out


def inspect(native, slr):
    if slr.get("revision_ref") != EXPECTED_SOURCE_REV:
        raise ValueError("wrong original GWB Wikipedia source revision")
    if native.get("source_revision") != EXPECTED_SOURCE_REV:
        raise ValueError("Rust native receipt source revision disagrees")
    if native.get("source_text_sha256") != EXPECTED_SOURCE_HASH:
        raise ValueError("wrong original GWB raw text digest")
    if native.get("engine_certification") != "EXPERIMENTAL_CANDIDATE_ONLY_OUTSIDE_CERTIFIED_DIRECT_PATH":
        raise ValueError("receipt is not the bounded experimental Rust candidate projection")
    original = _original_sentence_map(slr)
    observations = _array(native, "sentence_observations")
    if len(observations) != native.get("source_sentences") or len(original) != len(observations):
        raise ValueError("incomplete original sentence carrier")
    hist = Counter()
    examples = defaultdict(list)
    by_route = Counter()
    by_sentence = Counter()
    count_unsupported = 0
    total_candidates = total_alternatives = total_residuals = 0
    observed = set()
    unsupported_locations = set()
    for row in observations:
        s = row.get("sentence_index")
        if s not in original or s in observed:
            raise ValueError(f"non-source or duplicate native sentence {s}")
        observed.add(s)
        toks = original[s]
        candidate = _array(row, "candidates")
        alternatives = _array(row, "alternative_fibres")
        residuals = _array(row, "residuals")
        total_candidates += len(candidate)
        total_alternatives += len(alternatives)
        total_residuals += len(residuals)
        if row.get("projection_failures") != []:
            raise ValueError(f"projection failures in sentence {s}")
        for item in residuals:
            if item.get("kind") != "UnsupportedDependency":
                continue
            ordinal = item.get("token_ordinal")
            if not isinstance(ordinal, int) or not 0 <= ordinal < len(toks):
                raise ValueError(f"invalid original token ordinal: {s}:{ordinal}")
            if item.get("sentence_index") != s or item.get("consumer_closed") is not False:
                raise ValueError(f"promoted/wrong-source residual: {s}:{ordinal}")
            key = (s, ordinal)
            if key in unsupported_locations:
                raise ValueError(f"duplicated unsupported token {s}:{ordinal}")
            unsupported_locations.add(key)
            token = toks[ordinal]
            if not isinstance(token, dict):
                raise ValueError(f"wrong original token payload: {s}:{ordinal}")
            label = token.get("dep")
            surface = token.get("text")
            start = token.get("idx")
            if not isinstance(label, str) or not label or not isinstance(surface, str) or not isinstance(start, int):
                raise ValueError(f"missing original dependency/lexeme/offset: {s}:{ordinal}")
            hist[label] += 1
            by_sentence[s] += 1
            route = ROUTE.get(label, "notInHistoricalV04Taxonomy")
            by_route[route] += 1
            if len(examples[label]) < 3:
                examples[label].append({
                    "sentence_index": s, "token_ordinal": ordinal,
                    "surface": surface, "start_char": start,
                })
            count_unsupported += 1

    if (total_candidates, total_alternatives, total_residuals) != (
        native.get("native_candidate_count"),
        native.get("alternative_fibre_count"),
        native.get("typed_residual_count"),
    ):
        raise ValueError("original semantic count mismatch")
    if count_unsupported != sum(hist.values()) or count_unsupported != sum(by_route.values()):
        raise ValueError("fine diagnostic doesn't sum back to coarse")
    if len(observed) != len(original):
        raise ValueError("native receipt drops original source sentences")
    return {
        "schema": "gwb-same-source-unsupported-fine-audit-v1",
        "source_revision": EXPECTED_SOURCE_REV,
        "source_text_sha256": EXPECTED_SOURCE_HASH,
        "native_candidate_count": total_candidates,
        "native_alternative_site_count": total_alternatives,
        "native_residual_entry_count": total_residuals,
        "unsupported_dependency_count": count_unsupported,
        "unsupported_share_of_residual_entries": count_unsupported / total_residuals,
        "unsupported_coarse_refinement_exact": sum(hist.values()) == count_unsupported,
        "v04_source_owner": "DASHI/Cognition/PNF/SensibLawGWBv01UnsupportedResidualCertificationV04Exact.agda",
        "v04_work_routing_owner": "DASHI/Cognition/PNF/SensibLawUnsupportedDemandRoutingExact.agda",
        "v04_historical_scope": "41,044-sentence GWB tranche; do not import its measured counts as 643-sentence counts",
        "dependency_labels": dict(sorted(hist.items(), key=lambda x: (-x[1], x[0]))),
        "work_routes": dict(sorted(by_route.items())),
        "labels_outside_historical_v04": {
            label: count for label, count in sorted(hist.items())
            if label not in ROUTE
        },
        "sample_source_tokens_by_label": dict(sorted(examples.items())),
        "top_unsupported_sentence_indices": [
            {"sentence_index": s, "count": count}
            for s, count in by_sentence.most_common(20)
        ],
        "semantic_authority_created": False,
        "fix": "reuse canonical SensibLaw annotation graph/semantic reduction/PNF binding and original DASHI v0.4 diagnostic fibre; do not add a second parser",
    }


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--slr", type=Path, default=Path(".dashi/gwb-source/slr-record.json"))
    p.add_argument("--native", type=Path,
        default=Path("artifacts/gwb-semantic-proof/slr-rust-semantic-expansion.json"))
    p.add_argument("--output", type=Path)
    args = p.parse_args()
    result = inspect(json.loads(args.native.read_text(encoding="utf-8")),
                     json.loads(args.slr.read_text(encoding="utf-8")))
    text = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
    print(f"GWB_UNSUPPORTED_FINE_AUDIT_OK count={result['unsupported_dependency_count']} "
          f"labels={len(result['dependency_labels'])} "
          f"outside_v04={sum(result['labels_outside_historical_v04'].values())}")


if __name__ == "__main__":
    main()
