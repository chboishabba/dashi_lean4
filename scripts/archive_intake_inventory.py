#!/usr/bin/env python3
"""Inventory archive provenance and recursive Lean mirrors without extraction."""
from __future__ import annotations

import argparse
import csv
import hashlib
import os
import re
import tarfile
from collections import Counter
from pathlib import Path

EXTENSIONS = (".tar.gz", ".tgz", ".tar.xz", ".tar")
TITLE_NAMES = {"TOE_DASHI_HANDOFF_README.md", "TOE_CONSOLIDATION_BRIEF.md", "HANDOFF.md", "ARISTOTLE_SUMMARY.md", "README.md"}
FAMILIES = (
    "dashi_snapshot", "requestproject_snapshot", "spine", "synthesis", "cuisine",
    "integration", "promoted", "agda_mirror", "recursive_importedleans",
    "generated_output", "provenance", "imported_mirror", "other_lean",
)


def hash_stream(stream: object) -> str:
    digest = hashlib.sha256()
    while chunk := stream.read(1024 * 1024):
        digest.update(chunk)
    return digest.hexdigest()


def hash_file(path: Path) -> str:
    with path.open("rb") as stream:
        return hash_stream(stream)


def family_for(member_name: str) -> str:
    path = "/" + member_name.strip("/") + "/"
    for marker, family in (
        ("/Lean/ImportedLeans/", "recursive_importedleans"),
        ("/Lean/outputs/", "generated_output"),
        ("/Provenance/", "provenance"),
        ("/Lean/Imported/", "imported_mirror"),
        ("/Lean/AgdaMirror/", "agda_mirror"),
        ("/Lean/DASHI/", "dashi_snapshot"),
        ("/DASHI/output-final_aristotle/RequestProject/", "requestproject_snapshot"),
        ("/Lean/Spine/", "spine"),
        ("/Lean/Synthesis/", "synthesis"),
        ("/Lean/Cuisine/", "cuisine"),
        ("/Lean/Integration/", "integration"),
        ("/Lean/Promoted/", "promoted"),
    ):
        if marker in path:
            return family
    return "other_lean"


def archive_inventory(path: Path) -> tuple[dict[str, object], list[dict[str, object]]]:
    row: dict[str, object] = {
        "archive_filename": path.name, "tranche_title": "", "sha256": hash_file(path),
        "bytes": path.stat().st_size, "source_path": path, "top_level_roots": "",
        "integration_state": "untriaged",
    }
    family_counts: Counter[str] = Counter()
    members: list[dict[str, object]] = []
    lean_hashes: set[str] = set()
    lean_bytes = 0
    try:
        with tarfile.open(path, "r:*") as archive:
            archive_members = archive.getmembers()
            row["top_level_roots"] = ";".join(sorted({member.name.split("/", 1)[0] for member in archive_members if member.name}))
            for member in archive_members:
                if not member.isfile():
                    continue
                if Path(member.name).name in TITLE_NAMES and not row["tranche_title"]:
                    stream = archive.extractfile(member)
                    if stream is not None:
                        match = re.search(r"^#\s+(.+?)\s*$", stream.read(1024 * 1024).decode("utf8", "replace"), re.MULTILINE)
                        if match:
                            row["tranche_title"] = match.group(1)
                if not member.name.endswith(".lean"):
                    continue
                stream = archive.extractfile(member)
                if stream is None:
                    continue
                content_hash = hash_stream(stream)
                family = family_for(member.name)
                family_counts[family] += 1
                lean_hashes.add(content_hash)
                lean_bytes += member.size
                members.append({"archive_filename": path.name, "member_path": member.name,
                                "family": family, "bytes": member.size,
                                "content_sha256": content_hash})
    except (tarfile.TarError, OSError) as error:
        row["integration_state"] = f"unreadable:{type(error).__name__}"
    row.update(lean_files=len(members), lean_bytes=lean_bytes,
               unique_lean_content=len(lean_hashes),
               duplicate_lean_members=len(members) - len(lean_hashes))
    row.update({f"{family}_files": family_counts[family] for family in FAMILIES})
    return row, members


def open_csv(path: Path, fields: tuple[str, ...]) -> tuple[Path, object, csv.DictWriter]:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    handle = temporary.open("w", newline="", encoding="utf8")
    csv_writer = csv.DictWriter(handle, fieldnames=fields, lineterminator="\n")
    csv_writer.writeheader()
    return temporary, handle, csv_writer


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("roots", nargs="+", type=Path)
    parser.add_argument("--output", required=True, type=Path, help="archive-level CSV")
    parser.add_argument("--lean-members-output", type=Path, help="optional member-level Lean path/hash CSV")
    args = parser.parse_args()
    archives = sorted({path for root in args.roots for path in root.rglob("*")
                       if path.is_file() and path.name.lower().endswith(EXTENSIONS)})
    summary_fields = (
        "archive_filename", "tranche_title", "sha256", "bytes", "source_path", "top_level_roots",
        "integration_state", "lean_files", "lean_bytes", "unique_lean_content", "duplicate_lean_members",
        *(f"{family}_files" for family in FAMILIES),
    )
    member_fields = ("archive_filename", "member_path", "family", "bytes", "content_sha256")
    summary_tmp, summary_handle, summary_writer = open_csv(args.output, summary_fields)
    member_state = open_csv(args.lean_members_output, member_fields) if args.lean_members_output else None
    try:
        for archive in archives:
            summary, members = archive_inventory(archive)
            summary_writer.writerow(summary)
            if member_state:
                member_state[2].writerows(members)
    finally:
        summary_handle.close()
        if member_state:
            member_state[1].close()
    os.replace(summary_tmp, args.output)
    if member_state and args.lean_members_output:
        os.replace(member_state[0], args.lean_members_output)


if __name__ == "__main__":
    main()
