#!/usr/bin/env python3
"""Verify real GWB source-case witnesses, not invented semantic labels.

Source: committed original Rust receipt real_source_witnesses.
This is a source-shape diagnostic, NOT reviewed gold semantics.
"""
import argparse
import json
from pathlib import Path

CASES = {
  5: {"issue": "GWB-A03/A05", "tokens": {
    "Bush": "nsubj", "Welch": "dobj", "Laura": "compound",
    "librarian": "appos", "1977": "pobj"},
    "owners": ["SensibLaw/docs/architecture/PROOF_RELEVANT_IDENTITY_ACCEPTANCE.md",
               "SensibLaw/src/pnf/binding_candidate_sets.py"]},
  9: {"issue": "GWB-A02", "tokens": {
    "Bush": "nsubj", "sponsored": "ROOT", "increased": "amod",
    "set": "conj", "reformed": "conj"},
    "owners": ["SensibLaw/src/language/semantic_reductions.py",
               "DASHI/Cognition/PNF/SensibLawRoleTransitionManifoldExact.agda"]},
  18: {"issue": "GWB-A02/A04/A05/A06", "tokens": {
    "He": "nsubj", "it": "nsubj", "2003": "nummod",
    "overthrow": "xcomp", "citing": "advcl",
    "possessed": "acl", "had": "conj"},
    "owners": ["SensibLaw/src/pnf/binding_candidate_sets.py",
               "Docs/ITIRReopenableEvidenceHyperformalism.md"]},
  131: {"issue": "GWB-A05", "tokens": {
    "Presidency": "npadvmod", "2001–2009": "appos",
    "\n\n": "dep", "outlined": "ROOT"},
    "owners": ["SensibLaw/src/text/sentences.py",
               "SensibLaw/docs/wiki_revision_harness_contract_v0_1.md"]},
}

def inspect(receipt):
    rows = receipt.get("real_source_witnesses")
    if not isinstance(rows, list):
        raise ValueError("missing original source witness rows")
    witnesses = {row["sentence_index"]: row for row in rows}
    reports = []
    for sentence, case in CASES.items():
        if sentence not in witnesses:
            raise ValueError(f"original source witness missing: {sentence}")
        row = witnesses[sentence]
        tokens = row.get("source_token_map")
        if not isinstance(tokens, list):
            raise ValueError(f"source token map absent at sentence {sentence}")
        for surface, dependency in case["tokens"].items():
            matching = [token for token in tokens if
                        token.get("surface") == surface and token.get("dep") == dependency]
            if not matching:
                raise ValueError(f"original source dependency differs at {sentence}: {surface!r} expected {dependency!r}")
            for token in matching:
                a, b = token.get("source_span", [None, None])
                if not isinstance(a, int) or not isinstance(b, int) or not a < b:
                    raise ValueError(f"invalid source span at {sentence}: {surface}")
        if sentence == 131 and "\n\n" not in row.get("source_sentence", ""):
            raise ValueError("heading/paragraph witness no longer contains boundary")
        if sentence == 18:
            alt_ordinals = {a["token_ordinal"] for a in row["native_observation"]["alternative_fibres"]}
            token_ordinals = {t["surface"]: t["token_ordinal"] for t in tokens}
            if not {token_ordinals[x] for x in ("overthrow", "citing", "possessed")} <= alt_ordinals:
                raise ValueError("Iraq attribution alternatives dropped")
        reports.append({
            "sentence_index": sentence, "issue": case["issue"],
            "original_text": row["source_sentence"],
            "checked_token_dependencies": case["tokens"],
            "existing_owners": case["owners"], "source_witness_present": True,
            "semantics_concluded": False,
            "canonical_owner_has_been_run_for_this_sentence": False})
    return {
        "schema": "gwb-original-source-semantic-cases-v1",
        "source_revision": receipt.get("source_revision"),
        "source_text_sha256": receipt.get("source_text_sha256"),
        "cases": reports,
        "positive_semantic_gold_claimed": False, "not_a_second_parser": True}

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--native", type=Path,
        default=Path("artifacts/gwb-semantic-proof/slr-rust-semantic-expansion.json"))
    p.add_argument("--output", type=Path)
    args = p.parse_args()
    result = inspect(json.loads(args.native.read_text(encoding="utf-8")))
    raw = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(raw, encoding="utf-8")
    else:
        print(raw, end="")
    print(f"GWB_ORIGINAL_SEMANTIC_CASES_CHECKED count={len(result['cases'])} no_semantic_promotion=true")

if __name__ == "__main__":
    main()
