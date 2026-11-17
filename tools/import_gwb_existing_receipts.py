#!/usr/bin/env python3
"""One-time verified import of existing GWB proof TAR receipts directly to Git.

READ-only legacy TAR import: no new TAR, no NLP execution and no reproof.
The already executed native Rust/Lean logs are validated by the same strict
publisher used for future direct-to-Git proof runs. After successful commit,
the legacy TAR is optional and can be deleted by explicit flag.
"""
import argparse
import hashlib
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile

from publish_gwb_proof_receipts import (
    LOGS, NEGATIVE, RUST_NEGATIVE, PIN_SHA, publish,
)

SOURCE = (
    "article.html", "article.txt", "article-candidates.json", "slr-record.json",
    "slr-source-units.jsonl", "summary.md",
    "gwb_sensiblaw_p0b_mention_licences.json",
)
RESULT = (
    "proof/slr-rust-semantic-expansion.json",
    "proof/semantic_observer_audit.json",
    "proof/proof_run_manifest.json",
) + tuple("proof/" + n for n in LOGS) + tuple(
    "proof/rejected-" + n + ".log" for n in NEGATIVE
) + tuple("proof/rejected-slr-" + n + ".log" for n in RUST_NEGATIVE)


def main():
    p = argparse.ArgumentParser()
    p.add_argument("archive", type=Path)
    p.add_argument("--delete-on-success", action="store_true")
    p.add_argument("--no-commit", action="store_true")
    args = p.parse_args()
    repo = Path(__file__).resolve().parent.parent
    archive = args.archive.resolve()
    source = repo / ".dashi/gwb-source"
    source.parent.mkdir(parents=True, exist_ok=True)
    temp = Path(tempfile.mkdtemp(prefix=".gwb-import-", dir=repo / ".dashi"))
    try:
        with tarfile.open(archive, "r:") as tar:
            members = tar.getmembers()
            if len({m.name for m in members}) != len(members):
                raise ValueError("duplicate TAR members")
            if not all(m.isfile() for m in members):
                raise ValueError("unsafe legacy TAR member")
            names = {m.name for m in members}
            required = set(SOURCE) | set(RESULT)
            if not required.issubset(names):
                raise ValueError("legacy TAR lacks executed Rust/Lean proof receipts: " +
                                 ", ".join(sorted(required - names)))
            data_source = temp / "source"
            data_logs = temp / "run"
            data_source.mkdir()
            data_logs.mkdir()
            for name in SOURCE:
                (data_source / name).write_bytes(tar.extractfile(name).read())
            if hashlib.sha256((data_source / "article.txt").read_bytes()).hexdigest() != PIN_SHA:
                raise ValueError("legacy source SHA mismatch")
            for name in LOGS:
                (data_logs / name).write_bytes(
                    tar.extractfile("proof/" + name).read())
            for name in NEGATIVE:
                filename = "rejected-" + name + ".log"
                (data_logs / filename).write_bytes(
                    tar.extractfile("proof/" + filename).read())
            for name in RUST_NEGATIVE:
                filename = "rejected-slr-" + name + ".log"
                (data_logs / filename).write_bytes(
                    tar.extractfile("proof/" + filename).read())
            (data_logs / "slr-rust-observations.json").write_bytes(
                tar.extractfile("proof/slr-rust-semantic-expansion.json").read())
            (data_logs / "semantic_observer_audit.json").write_bytes(
                tar.extractfile("proof/semantic_observer_audit.json").read())
            import json
            previous = json.load(tar.extractfile("proof/proof_run_manifest.json"))
            slr_head = previous.get("rust_source_repo_head")
            lean_version = previous.get("lean_version")
            jmd_head_at_run = previous.get("git_head")
            if not slr_head or not lean_version or not jmd_head_at_run:
                raise ValueError("missing original run's exact Rust/Lean provenance")
        # Never overwrite an existing original fixture of different bytes.
        if source.exists():
            for name in SOURCE:
                if (source / name).read_bytes() != (data_source / name).read_bytes():
                    raise ValueError("existing source fixture differs: " + name)
        else:
            data_source.rename(source)
        # Publish the REAL captured run, no Rust or Lean rerun.
        publish(repo, source, data_logs, slr_head, lean_version,
                not args.no_commit, jmd_head_at_run=jmd_head_at_run)
        print("GWB_LEGACY_TAR_RECEIPTS_IMPORTED_TO_GIT")
        if args.delete_on_success:
            if args.no_commit:
                raise ValueError("will not delete TAR unless Git commit enabled")
            # A Git commit must have succeeded, not just an output copy.
            status = subprocess.check_output(
                ["git", "-C", str(repo), "status", "--porcelain", "--",
                 "artifacts/gwb-semantic-proof"], text=True)
            if status.strip():
                raise ValueError("Git receipt directory still uncommitted; retain TAR")
            archive.unlink()
            print("GWB_LEGACY_TAR_DELETED_AFTER_VERIFIED_COMMIT")
    finally:
        shutil.rmtree(temp, ignore_errors=True)

if __name__ == "__main__":
    main()
