#!/usr/bin/env python3
"""Build a provenance-preserving, content-addressed Aristotle source corpus."""

from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import sys
import tarfile
from collections import Counter
from datetime import UTC, datetime
from pathlib import Path, PurePosixPath


REPO = Path(__file__).resolve().parents[1]
CORPUS = REPO / "ImportedLeans" / "aristotle-results" / "canonical-corpus"
ROOTS = (
    Path("/home/c/Downloads"),
    Path("/home/c/Documents/code/aristotle-cli-rs"),
    Path("/home/c/Documents/code/aristotle-cli-tmp"),
    Path("/home/c/Documents/code/aristotle-toe-result-bf6411b6"),
    Path("/home/c/Documents/code/aristotle-cuisine-result-2c3d9d4c"),
)
ARCHIVE_SUFFIXES = (".tar", ".tar.gz", ".tgz", ".tar.zst")
SOURCE_SUFFIXES = {
    ".lean", ".agda", ".pdf", ".md", ".markdown", ".rst", ".txt",
    ".sh", ".bash", ".py", ".rs", ".toml", ".json", ".yaml", ".yml",
    ".xml", ".csv", ".tex", ".bib", ".nix", ".make",
}
SOURCE_NAMES = {"makefile", "dockerfile", "license", "copying", "readme", "manifest"}
EXCLUDED_PARTS = {".git", ".lake", "target", "build", "_build", "dist", "node_modules", ".venv", "venv", "__pycache__", ".cache", ".agda", "malonzo", ".autonomous-orchestrator"}
UUID_RE = re.compile(r"[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}", re.I)


def candidate_archives() -> list[Path]:
    found: set[Path] = set()
    for root in ROOTS:
        if not root.is_dir():
            continue
        for path in root.rglob("*"):
            if not path.is_file() or not path.name.lower().endswith(ARCHIVE_SUFFIXES):
                continue
            rel = path.relative_to(root)
            if any(part in EXCLUDED_PARTS for part in rel.parts):
                continue
            lower = str(rel).lower()
            # Downloads contain many unrelated archives; sibling project roots are in scope.
            if root.name == "Downloads" and "aristotle" not in lower:
                continue
            if root.name == "aristotle-cli-rs" and not (
                "aristotle" in lower or path.name in {"result-1.tar.gz", "result-2.tar.gz"} or "attachments" in rel.parts
            ):
                continue
            found.add(path.resolve())
    return sorted(found, key=lambda p: str(p))


def is_source(member: tarfile.TarInfo) -> tuple[bool, str | None]:
    path = PurePosixPath(member.name)
    parts = set(path.parts)
    excluded = sorted(parts & EXCLUDED_PARTS)
    if excluded:
        return False, excluded[0]
    name = path.name.lower()
    return name in SOURCE_NAMES or path.suffix.lower() in SOURCE_SUFFIXES, None


def safe_member_path(name: str) -> Path | None:
    path = PurePosixPath(name)
    if path.is_absolute() or ".." in path.parts:
        return None
    return Path(*path.parts)


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def archive_id(path: Path, archive_hash: str) -> str:
    stem = path.name
    for suffix in ARCHIVE_SUFFIXES:
        if stem.lower().endswith(suffix):
            stem = stem[: -len(suffix)]
            break
    return f"{stem}--{archive_hash[:12]}"


def source_metadata(member_name: str, data: bytes) -> dict[str, str]:
    text = data[:65536].decode("utf-8", errors="ignore")
    metadata: dict[str, str] = {}
    request = UUID_RE.search(member_name + "\n" + text)
    if request:
        metadata["request_id"] = request.group(0)
    for pattern, key in ((r"(?:commit|revision)\\s*[:=]\\s*([0-9a-f]{7,40})", "source_commit"),
                         (r"(?:version|release)\\s*[:=]\\s*([^\\s,]+)", "source_version")):
        match = re.search(pattern, text, re.I)
        if match:
            metadata[key] = match.group(1)
    return metadata


def main() -> int:
    archives = candidate_archives()
    if not archives:
        print("no archives found", file=sys.stderr)
        return 1
    shutil.rmtree(CORPUS, ignore_errors=True)
    blobs = CORPUS / "blobs" / "sha256"
    blobs.mkdir(parents=True)
    records: list[dict[str, object]] = []
    archive_rows: list[dict[str, object]] = []
    hashes: dict[str, str] = {}
    for archive in archives:
        archive_hash = sha256_file(archive)
        row: dict[str, object] = {
            "archive_id": archive_id(archive, archive_hash),
            "path": str(archive),
            "sha256": archive_hash,
            "size_bytes": archive.stat().st_size,
            "modified_at": datetime.fromtimestamp(archive.stat().st_mtime, UTC).isoformat(),
            "imported": False,
            "members": 0,
            "source_members": 0,
            "excluded_members": {},
            "errors": [],
        }
        excluded: Counter[str] = Counter()
        try:
            with tarfile.open(archive, "r:*") as tar:
                for member in tar:
                    if not member.isfile():
                        continue
                    row["members"] = int(row["members"]) + 1
                    allowed, excluded_reason = is_source(member)
                    if not allowed:
                        if excluded_reason:
                            excluded[excluded_reason] += 1
                        continue
                    safe_path = safe_member_path(member.name)
                    if safe_path is None:
                        excluded["unsafe_path"] += 1
                        continue
                    extracted = tar.extractfile(member)
                    if extracted is None:
                        continue
                    data = extracted.read()
                    content_hash = hashlib.sha256(data).hexdigest()
                    blob = blobs / content_hash[:2] / content_hash
                    if not blob.exists():
                        blob.parent.mkdir(parents=True, exist_ok=True)
                        blob.write_bytes(data)
                    hashes.setdefault(content_hash, str(blob.relative_to(CORPUS)))
                    record: dict[str, object] = {
                        "archive_id": row["archive_id"],
                        "archive_sha256": archive_hash,
                        "member": str(safe_path),
                        "size_bytes": len(data),
                        "sha256": content_hash,
                        "blob": hashes[content_hash],
                    }
                    record.update(source_metadata(member.name, data))
                    records.append(record)
                    row["source_members"] = int(row["source_members"]) + 1
                    row["imported"] = True
        except (tarfile.TarError, OSError) as error:
            row["errors"] = [str(error)]
        row["excluded_members"] = dict(sorted(excluded.items()))
        archive_rows.append(row)
        print(f"{row['archive_id']}: {row['source_members']} source members", flush=True)
    records.sort(key=lambda r: (str(r["archive_id"]), str(r["member"])))
    manifest = {
        "schema": "dashi-aristotle-corpus-v1",
        "generated_at": datetime.now(UTC).isoformat(),
        "policy": {
            "included": sorted(SOURCE_SUFFIXES) + sorted(SOURCE_NAMES),
            "excluded_generated_paths": sorted(EXCLUDED_PARTS),
            "storage": "content-addressed blobs; every source occurrence is retained in records.json",
        },
        "summary": {
            "archives_discovered": len(archive_rows),
            "archives_imported": sum(bool(row["imported"]) for row in archive_rows),
            "source_occurrences": len(records),
            "unique_content_blobs": len(hashes),
            "duplicate_occurrences": len(records) - len(hashes),
        },
        "archives": archive_rows,
    }
    (CORPUS / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    records_dir = CORPUS / "records"
    records_dir.mkdir()
    # GitHub rejects a single provenance index above 100 MB.  JSON Lines shards
    # retain one complete occurrence per line and keep the index streamable.
    shard_size = 100_000
    for index in range(0, len(records), shard_size):
        shard = records_dir / f"records-{index // shard_size + 1:04d}.jsonl"
        with shard.open("w", encoding="utf-8") as handle:
            for record in records[index : index + shard_size]:
                handle.write(json.dumps(record, sort_keys=True) + "\n")
    (CORPUS / "README.md").write_text(
        "# Canonical Aristotle source corpus\n\n"
        "`manifest.json` inventories every in-scope archive and the generated-content exclusions. "
        "The `records/` JSON Lines shards map every original archive member to one content-addressed file under `blobs/sha256/`. "
        "This preserves request/version provenance without silently overwriting older results. Raw archives are intentionally not committed.\n",
        encoding="utf-8",
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
