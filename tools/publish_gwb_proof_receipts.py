#!/usr/bin/env python3
"""Publish only executed GWB Rust/Lean evidence to versioned Git files.

The original 25 MB source/P0b fixture stays in the ignored project-local
source directory; it is not a new NLP producer or Git artifact. No TAR created.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

PIN_SHA = "a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233"
PIN_REV = "enwiki-revid:1385850169"
OUTPUT = Path("artifacts/gwb-semantic-proof")
LOGS = (
    "jmd-targeted-prerequisites-build.log",
    "source-consumer-build.log", "native-fibre-lean-build.log",
    "typed-semantic-fibre-build.log", "q207-identity-proof-build.log",
    "lean-build.log", "axiom-audit.log", "consumer-fibre-proof.log",
    "db-m12-s28-build.log", "jmd-property-proof-build.log",
    "world-graph-proof-build.log", "hyperfabric-proof-build.log",
    "article-system-proof-build.log", "p4-source-licence-build.log",
    "finite-consumer-build.log",
    "proof-composition-build.log",
    "proof-composition-proof.log",
    "p4-source-licence-proof.log",
    "article-source-proof.log", "semantic-scope-proof.log",
    "native-fibre-source-proof.log", "slr-rust-test.log",
    "slr-rust-expansion.log",
)
NEGATIVE = (
    "missing-predicate", "missing-direct-actor", "false-year-index",
    "promoted-world-truth", "forged-paragraph-boundary",
)
RUST_NEGATIVE = (
    "passive-by-as-actor", "event-date-falsely-closed", "forged-occurrence",
    "dropped-ambiguity", "false-residual-closure",
)
MARKERS = {
    "consumer-fibre-proof.log": "GWB_FIBRE_THEOREMS_KERNEL_OK",
    "proof-composition-proof.log": "GWB_FINITE_CONSUMER_COMPOSITION_KERNEL_OK",
    "p4-source-licence-proof.log": "GWB_P4_SOURCE_THEOREMS_KERNEL_OK",
    "article-source-proof.log": "JMD_LEAN_SOURCE_PROOF_OK sha256=" + PIN_SHA,
    "semantic-scope-proof.log": "GWB_REAL_SOURCE_FLAT_SCOPE_NONFACTORABILITY_PROVED",
    "native-fibre-source-proof.log": "GWB_RUST_FIBRE_AND_CONSUMER_SOURCE_BOUND_LEAN_PASS",
    "slr-rust-expansion.log": "GWB_SLR_RUST_SEMANTIC_EXPANSION_PARITY_PASS",
}
MAX_RECEIPT_BYTES = 15 * 1024 * 1024


def require(ok, msg):
    if not ok:
        raise ValueError(msg)


def git(root, *args):
    return subprocess.check_output(["git", "-C", str(root), *args],
                                   text=True).strip()


def publish(repo, source, run, slr_head, lean_version, auto_commit,
            jmd_head_at_run=None):
    article = (source / "article.txt").read_bytes()
    require(hashlib.sha256(article).hexdigest() == PIN_SHA,
            "original raw UTF-8 source digest mismatch")
    original = json.loads((source / "slr-record.json").read_bytes())
    require(original["revision_ref"] == PIN_REV, "source revision mismatch")
    audit = json.loads((run / "semantic_observer_audit.json").read_bytes())
    require(audit["source_utf8_sha256"] == PIN_SHA and
            audit["embedded_parent_conjunctions"] == 57 and
            audit["unmaterialized_grammatical_role_tokens"] == 73,
            "real-source semantic audit not accepted")
    native_path = run / "slr-rust-observations.json"
    require(native_path.stat().st_size <= MAX_RECEIPT_BYTES,
            "native semantic receipt >15 MiB; inspect before committing")
    native = json.loads(native_path.read_bytes())
    require(native["schema"] == "gwb-slr-native-semantic-expansion-observations-v1" and
            native["source_text_sha256"] == PIN_SHA and
            native["source_sentences"] == 643 and native["source_tokens"] == 17547 and
            native["direct_reference_parity_complete"] is True and
            native["projection_failures"] == 0, "real SLR parity not established")
    require(native["source_sentences"] == len(native["sentence_observations"]),
            "missing sentence fibre observations")
    for field, key in (("candidates", "native_candidate_count"),
                       ("alternative_fibres", "alternative_fibre_count"),
                       ("residuals", "typed_residual_count")):
        require(sum(len(row[field]) for row in native["sentence_observations"]) ==
                native[key], "fibre/residual count mismatch: " + key)
    require(native["consumer_specific_semantic_licence_paid"] is False and
            native["full_production_s28_or_hyperfabric_closure"] is False and
            native["world_occurrence_paid"] is False,
            "Rust receipt fabricated semantic review or world truth")
    require(native["real_source_contract_checks"]["passive_by_as_unresolved_reference"] == 62 and
            native["real_source_contract_checks"]["iraq_claim_possessed_had_ambiguity_preserved"],
            "real original GWB syntactic semantic gates failed")

    consumers = native["consumer_adequacy"]
    original_claim = next(row["claim_candidate_id"]
                          for row in original["pnf_candidates"]
                          if row["sentence_index"] == 18)
    require(consumers["semantic_target_ref"] == original_claim and
            consumers["factors_through_kernel_proof_paid"] is False,
            "consumer receipt is not tied to real GWB source claim")
    outcomes = {r["query_ref"]: r for r in consumers["runtime_outcomes"]}
    require(len(outcomes) == 5, "incomplete consumer output")
    for key in ("gwb:source:observed-mentions",
                "gwb:source:syntactic-role-candidates"):
        require(outcomes[key]["disposition"] == "Adequate",
                "source observation consumer incomplete")
    for key in ("gwb:person:who-was-agent", "gwb:event:when",
                "gwb:world:occurrence"):
        require(outcomes[key]["disposition"] == "NeedsResearch" and
                "SemanticIdentity" in outcomes[key]["missing_axes"] and
                outcomes[key]["research_demands"],
                "identity/world consumer silently closed")
    require("Temporal" in outcomes["gwb:event:when"]["missing_axes"] and
            "FactualPredicate" in outcomes["gwb:world:occurrence"]["missing_axes"],
            "temporal or factual axis falsely paid")

    all_logs = LOGS + tuple("rejected-" + n + ".log" for n in NEGATIVE) + tuple(
        "rejected-slr-" + n + ".log" for n in RUST_NEGATIVE)
    for name in all_logs:
        require((run / name).is_file(), "missing executed proof/negative log: " + name)
    # A failing subprocess is not sufficient: every adversarial control
    # must be rejected by the intended Lean source/semantic checker, not
    # by a crash, missing dependency or malformed runner invocation.
    for negative in NEGATIVE:
        name = "rejected-" + negative + ".log"
        log = (run / name).read_bytes()
        require(b"JMD Lean rejected a forged or unsupported source/PNF projection" in log,
                "adversarial source control failed for the wrong reason: " + name)
    for negative in RUST_NEGATIVE:
        name = "rejected-slr-" + negative + ".log"
        log = (run / name).read_bytes()
        require(b"GWB_RUST_FIBRE_LEAN_REJECTED:" in log,
                "adversarial semantic control failed for the wrong reason: " + name)
    require(b"GWB_ARTICLE_LOCAL_SYSTEM_THEOREM_KERNEL_OK" in
            (run / "proof-composition-proof.log").read_bytes(),
            "end-to-end conditional article theorem was not loaded in Lean")
    require(b"GWB_P4_SOURCE_LICENCE_KERNEL_OK" in
            (run / "native-fibre-source-proof.log").read_bytes(),
            "real typed-source P4 positive SourceQueryLicence was not executed")
    require(b"GWB_TYPED_SEMANTIC_FIBRE_LEAN_PASS" in
            (run / "native-fibre-source-proof.log").read_bytes(),
            "typed SLR candidate/alternative/residual decoder was not executed")
    for name, marker in MARKERS.items():
        require(marker.encode() in (run / name).read_bytes(), "missing " + marker)
    require(b"sorryAx" not in (run / "axiom-audit.log").read_bytes() and
            b"admitAx" not in (run / "axiom-audit.log").read_bytes(),
            "Lean proof contains a sorry/admit axiom")

    receipt_head = jmd_head_at_run or git(repo, "rev-parse", "HEAD")
    manifest = {
        "schema": "gwb-committed-rust-lean-proof-v1",
        "source_revision": PIN_REV,
        "source_utf8_sha256": PIN_SHA,
        "jmd_head_at_run": receipt_head,
        "receipt_imported_or_published_at_head":
            git(repo, "rev-parse", "HEAD"),
        "slr_head_at_run": slr_head,
        "lean_version": lean_version,
        "slr_semantic_expansion": "EXECUTED_CANDIDATE_ONLY",
        "source_sentences": native["source_sentences"],
        "source_tokens": native["source_tokens"],
        "candidates": native["native_candidate_count"],
        "alternative_fibres": native["alternative_fibre_count"],
        "typed_residuals": native["typed_residual_count"],
        "direct_reference_parity": True,
        "lean_source_fibre_receipt": "PASSED",
        "finite_consumer_composition": "KERNEL_PROVED_CONDITIONAL_ON_SEMANTIC_COVERAGE",
        "negative_controls_rejected": len(NEGATIVE) + len(RUST_NEGATIVE),
        "reviewed_semantic_transports": "NOT_TESTED",
        "production_db_s28": "NOT_TESTED",
        "full_consumer_factors_through_certificate": "NOT_PAID",
        "historical_occurrence": "NOT_LICENSED",
        "source_fixture": "local ignored .dashi/gwb-source, not committed",
    }

    dest = repo / OUTPUT
    dest.parent.mkdir(parents=True, exist_ok=True)
    temp = Path(tempfile.mkdtemp(prefix=".gwb-results-", dir=dest.parent))
    try:
        # Full source-bound candidate/fibre/residual output is retained;
        # operator can inspect every sentence without regenerating a TAR.
        shutil.copyfile(native_path, temp / "slr-rust-semantic-expansion.json")
        shutil.copyfile(run / "semantic_observer_audit.json",
                        temp / "semantic_observer_audit.json")
        for name in all_logs:
            shutil.copyfile(run / name, temp / name)
        (temp / "proof_run_manifest.json").write_text(
            json.dumps(manifest, sort_keys=True, indent=2) + "\n",
            encoding="utf-8")
        require(sum(f.stat().st_size for f in temp.iterdir()) <=
                20 * 1024 * 1024,
                "generated receipts exceed 20 MiB; review before committing")
        # No partial replacement of the public receipt tree on failed checks.
        backup = dest.parent / (".gwb-proof-backup-" + str(os.getpid()))
        had_previous = dest.exists()
        if had_previous:
            os.replace(dest, backup)
        try:
            os.replace(temp, dest)
        except BaseException:
            if had_previous:
                os.replace(backup, dest)
            raise
        if had_previous:
            shutil.rmtree(backup)
    finally:
        if temp.exists():
            shutil.rmtree(temp)

    print("GWB_GIT_RECEIPTS_VERIFIED", OUTPUT)
    if auto_commit:
        # Commit exactly the proof results, not unrelated staged changes.
        subprocess.run(["git", "-C", str(repo), "add", "-A", "--",
                        str(OUTPUT)], check=True)
        diff = subprocess.run(["git", "-C", str(repo), "diff", "--cached",
                               "--quiet", "--", str(OUTPUT)])
        if diff.returncode == 1:
            subprocess.run(["git", "-C", str(repo), "commit", "-m",
                            "Record kernel-checked GWB SLR fibre and consumer evidence",
                            "--only", "--", str(OUTPUT)], check=True)
        else:
            require(diff.returncode == 0, "git diff failed")
            print("GWB_GIT_RECEIPTS_UNCHANGED")
    else:
        print("GWB_GIT_RECEIPTS_READY_FOR_GIT_ADD", OUTPUT)


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("--repo", required=True, type=Path)
    p.add_argument("--source", required=True, type=Path)
    p.add_argument("--run", required=True, type=Path)
    p.add_argument("--slr-head", required=True)
    p.add_argument("--lean-version", required=True)
    p.add_argument("--no-commit", action="store_true")
    a = p.parse_args()
    publish(a.repo.resolve(), a.source.resolve(), a.run.resolve(),
            a.slr_head, a.lean_version, not a.no_commit)
