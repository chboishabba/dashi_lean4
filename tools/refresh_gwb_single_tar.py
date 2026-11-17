#!/usr/bin/env python3
"""Atomically refresh the SAME original GWB TAR with evidence and proof receipts.

No NLP, no semantic producer, no claimed semantic admission. Read-only inputs;
a replace-on-success archive is the only persistent generated artifact.
"""
import argparse
import hashlib
import io
import json
import os
from pathlib import Path
import tarfile
import tempfile
from gwb_semantic_observer_audit import check as audit_source, load as load_source

PINNED_SOURCE_SHA256 = "a88ef63b9c109f0f09c2fc2a266373a9ecaae855104cb0e11c4e6c53d90d3233"
PINNED_REVISION = "enwiki-revid:1385850169"
ORIGINAL = (
    "article.html", "article.txt", "article-candidates.json", "slr-record.json",
    "slr-source-units.jsonl", "summary.md",
    "gwb_sensiblaw_p0b_mention_licences.json",
)
AUDIT = "proof/semantic_observer_audit.json"
SUMMARY = "proof/semantic_observer_audit.md"
MANIFEST = "proof/proof_run_manifest.json"
LOGS = ("lean-build.log", "axiom-audit.log",
        "consumer-fibre-proof.log", "article-source-proof.log",
        "semantic-scope-proof.log")

def require(ok, error):
    if not ok:
        raise ValueError(error)

def pack(path, report, logs=None, lean_version=None, head=None):
    archive_path = Path(path).resolve()
    report_path = Path(report).resolve()
    payload = json.loads(report_path.read_text(encoding="utf-8"))
    require(payload["schema"] == "gwb-consumer-observer-evidence-audit-v1",
            "audit evidence schema")
    require(payload["source_revision"] == PINNED_REVISION, "audit revision")
    require(payload["source_utf8_sha256"] == PINNED_SOURCE_SHA256,
            "audit source digest")
    require(payload == audit_source(*load_source(str(archive_path))),
            "supplied semantic audit is not derived from original TAR evidence")
    additional = {AUDIT: report_path.read_bytes()}
    status = "NOT_EXECUTED_IN_THIS_REFRESH"
    if logs is not None:
        root = Path(logs)
        for name in LOGS:
            file_path = root / name
            require(file_path.is_file(), "missing Lean proof log: " + name)
            additional["proof/" + name] = file_path.read_bytes()
        require(b"GWB_FIBRE_THEOREMS_KERNEL_OK" in
                additional["proof/consumer-fibre-proof.log"],
                "no kernel-fibre success in log")
        require(b"JMD_LEAN_SOURCE_PROOF_OK sha256=" +
                PINNED_SOURCE_SHA256.encode("ascii") in
                additional["proof/article-source-proof.log"],
                "no exact-source success in log")
        require(b"GWB_REAL_SOURCE_FLAT_SCOPE_NONFACTORABILITY_PROVED" in
                additional["proof/semantic-scope-proof.log"],
                "actual source-backed scope theorem did not run")
        require(b"sorryAx" not in additional["proof/axiom-audit.log"] and
                b"admitAx" not in additional["proof/axiom-audit.log"],
                "axiom audit contains admitted proof")
        for name in ("missing-predicate", "missing-direct-actor",
                     "false-year-index", "promoted-world-truth",
                     "forged-paragraph-boundary"):
            require((root / ("rejected-" + name + ".log")).is_file(),
                    "missing counterexample rejection log: " + name)
            additional["proof/rejected-" + name + ".log"] = (
                root / ("rejected-" + name + ".log")).read_bytes()
        status = "TARGETED_LEAN_SOURCE_SCOPE_AND_FIVE_NEGATIVE_CONTROLS_RUN"
    manifest = {
        "schema": "gwb-single-tar-proof-manifest-v1",
        "source_revision": PINNED_REVISION,
        "original_article_utf8_sha256": PINNED_SOURCE_SHA256,
        "lean_proof_status": status,
        "lean_version": lean_version if logs else None,
        "git_head": head if logs else None,
        "source_observation_consistency": "ARCHIVE_AUDITED",
        "production_rust_semantic_fibre": "NOT_IN_INPUT_ARCHIVE",
        "reviewed_s28_event_join": "NOT_IN_INPUT_ARCHIVE",
        "consumer_relative_semantic_closure": "NOT_IN_INPUT_ARCHIVE",
        "world_event_occurrence": "NOT_LICENSED",
        "semantics_report": AUDIT,
        "proof_logs_are_part_of_same_tar": logs is not None,
    }
    additional[MANIFEST] = (json.dumps(manifest, indent=2, sort_keys=True)
                            + "\n").encode("utf-8")
    md = [
        "# Source-grounded GWB consumer-observer audit",
        "",
        "No parser or semantics were rerun. The original dependency tokens and",
        "P0b mention candidates were inspected without an admission effect.",
        "",
        f"Revision: \`{PINNED_REVISION}\`.",
        f"Canonical raw text SHA-256: \`{PINNED_SOURCE_SHA256}\`.",
        "",
        f"Nested coordinated predicates: {payload['embedded_parent_conjunctions']}.",
        f"Flat scope labels masking embedding: {payload['embedded_conjunction_flat_assertion_labels']}.",
        f"Syntactic role positions without a P0b mention: {payload['unmaterialized_grammatical_role_tokens']}.",
        "",
        "Query 'is this conjunction under an embedded predicate?' is not",
        "a function of the flattened scope label alone: see JSON witnesses.",
        "Original source rows retain the distinction.",
        "",
        "The real SLR semantic-fibre ledger and reviewer receipts are absent.",
        "A targeted abstract Lean theorem is not a real-article semantic closure.",
        "",
        f"Targeted Lean in this refresh: {status}.",
        ""
    ]
    additional[SUMMARY] = "\n".join(md).encode("utf-8")
    fd, temp_path = tempfile.mkstemp(
        prefix=".gwb-single-tar-", suffix=".tar", dir=archive_path.parent)
    os.close(fd)
    try:
        with tarfile.open(archive_path, "r:") as old:
            old_names = old.getnames()
            require(len(old_names) == len(set(old_names)),
                    "duplicate entries in original TAR")
            require(all(x in old_names for x in ORIGINAL),
                    "missing required original article evidence")
            require(all(m.isfile() for m in old.getmembers()),
                    "not a flat regular-file TAR")
            with tarfile.open(temp_path, "w:") as new:
                for name in old_names:
                    if name in additional or name.startswith("proof/"):
                        continue
                    item = old.getmember(name)
                    data = old.extractfile(item).read()
                    if name == "article.txt":
                        require(hashlib.sha256(data).hexdigest() ==
                                PINNED_SOURCE_SHA256, "original text changed")
                    if name == "slr-record.json":
                        require(json.loads(data)["revision_ref"] ==
                                PINNED_REVISION, "SLR revision changed")
                    new.addfile(item, io.BytesIO(data))
                for name, data in sorted(additional.items()):
                    entry = tarfile.TarInfo(name)
                    entry.size = len(data)
                    entry.mode = 0o644
                    entry.mtime = 0
                    new.addfile(entry, io.BytesIO(data))
        with tarfile.open(temp_path) as check, tarfile.open(archive_path) as old:
            require(check.getnames().count(MANIFEST) == 1,
                    "failed to build canonical proof manifest")
            for name in ORIGINAL:
                require(check.extractfile(name).read() ==
                        old.extractfile(name).read(),
                        "original input evidence bytes not retained: " + name)
        os.replace(temp_path, archive_path)
    finally:
        if os.path.exists(temp_path):
            os.unlink(temp_path)
    print("GWB_SINGLE_TAR_REFRESH_OK", archive_path, status)

if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("tar")
    p.add_argument("--audit", required=True)
    p.add_argument("--logs")
    p.add_argument("--lean-version")
    p.add_argument("--head")
    a = p.parse_args()
    pack(a.tar, a.audit, a.logs, a.lean_version, a.head)
