#!/usr/bin/env python3
"""Regression test for recursive Lean archive inventory."""
from __future__ import annotations

import csv
import io
import subprocess
import sys
import tarfile
import tempfile
from pathlib import Path


def add_text(archive: tarfile.TarFile, name: str, text: str) -> None:
    data = text.encode()
    info = tarfile.TarInfo(name)
    info.size = len(data)
    archive.addfile(info, io.BytesIO(data))


def main() -> None:
    script = Path(__file__).with_name("archive_intake_inventory.py")
    with tempfile.TemporaryDirectory() as raw:
        root = Path(raw)
        archive_path = root / "fixture.tar.gz"
        with tarfile.open(archive_path, "w:gz") as archive:
            add_text(archive, "output/Lean/DASHI/Surface.lean", "def canonical := 1\n")
            add_text(archive, "output/Lean/ImportedLeans/copy.lean", "def canonical := 1\n")
            add_text(archive, "output/Lean/outputs/generated.lean", "def generated := 2\n")
            add_text(archive, "output/Provenance/receipt.lean", "def receipt := 3\n")
            add_text(archive, "output-final_aristotle/RequestProject/Main.lean", "def handoff := 4\n")
            add_text(archive, "output/HANDOFF.md", "# Fixture tranche\n")
        summary = root / "summary.csv"
        members = root / "members.csv"
        subprocess.run(
            [sys.executable, str(script), str(root), "--output", str(summary),
             "--lean-members-output", str(members)],
            check=True,
        )
        with summary.open(newline="") as handle:
            row = next(csv.DictReader(handle))
        assert row["lean_files"] == "5", row
        assert row["unique_lean_content"] == "4", row
        assert row["duplicate_lean_members"] == "1", row
        assert row["recursive_importedleans_files"] == "1", row
        assert row["generated_output_files"] == "1", row
        assert row["provenance_files"] == "1", row
        assert row["requestproject_snapshot_files"] == "1", row
        with members.open(newline="") as handle:
            families = {row["member_path"]: row["family"] for row in csv.DictReader(handle)}
        assert families["output/Lean/DASHI/Surface.lean"] == "dashi_snapshot"
        assert families["output/Lean/ImportedLeans/copy.lean"] == "recursive_importedleans"
        assert families["output-final_aristotle/RequestProject/Main.lean"] == "requestproject_snapshot"


if __name__ == "__main__":
    main()
