#!/usr/bin/env python3
"""Classify every file in `Lean/Imported` by the rung it reaches.

The rungs are those of `Integration.CorpusPromotion.Stage`:

    ingested < elaborates < wired < audited < cited

This script decides the first two mechanically and reports the rest as not
attempted, which is the honest answer: nothing under `Lean/Imported` is a module
of a library in `lakefile.toml`, so nothing there is `wired` or beyond.

* `ingested`      — the file is in the tree (every file, by construction).
* `elaborates`    — `lake env lean <file>` exits 0 in *this* toolchain.
* `fails`         — it exits non-zero; the first error line is recorded.
* `not-attempted` — it imports a module that is not Mathlib and not in this
                    project, i.e. it needs its own library root first.

A file that elaborates but contains `sorry` is marked `elaborates-with-sorry`:
elaboration is not a proof.

Usage:  python3 scripts/promotion_status.py [--jobs N] [--limit N]
Writes: Lean/Imported/PROMOTION_STATUS.csv
"""

from __future__ import annotations

import argparse
import csv
import os
import re
import subprocess
from concurrent.futures import ThreadPoolExecutor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
IMPORTED = os.path.join(ROOT, "Lean", "Imported")
SORRY = re.compile(r"\bsorry\b|\badmit\b")


def imports(path: str) -> list[str]:
    out = []
    with open(path, errors="ignore") as handle:
        for line in handle:
            if line.startswith("import "):
                out.append(line.split()[1].strip())
            elif line.strip() and not line.startswith("--"):
                # imports must come first; stop at the first real declaration
                if out:
                    break
    return out


def self_contained(imps: list[str]) -> bool:
    return bool(imps) and all(i == "Mathlib" or i.startswith("Mathlib.") for i in imps)


def has_sorry(path: str) -> bool:
    with open(path, errors="ignore") as handle:
        for line in handle:
            code = line.split("--")[0]
            if SORRY.search(code):
                return True
    return False


def classify(rel: str, timeout: int) -> tuple[str, str, str]:
    path = os.path.join(IMPORTED, rel)
    imps = imports(path)
    if not self_contained(imps):
        return rel, "not-attempted", "needs a library root beyond Mathlib"
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", os.path.join("Lean", "Imported", rel)],
            cwd=ROOT, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return rel, "fails", f"timeout after {timeout}s"
    if proc.returncode != 0:
        first = next((l for l in proc.stdout.splitlines() if "error" in l), "")
        return rel, "fails", first[:200]
    return rel, ("elaborates-with-sorry" if has_sorry(path) else "elaborates"), ""


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--jobs", type=int, default=6)
    parser.add_argument("--limit", type=int, default=0)
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()

    files = []
    for dirpath, _, names in os.walk(IMPORTED):
        for name in names:
            if name.endswith(".lean"):
                files.append(os.path.relpath(os.path.join(dirpath, name), IMPORTED))
    files.sort()
    if args.limit:
        files = files[: args.limit]

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        rows = list(pool.map(lambda f: classify(f, args.timeout), files))

    out = os.path.join(IMPORTED, "PROMOTION_STATUS.csv")
    with open(out, "w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["path", "rung", "note"])
        writer.writerows(rows)

    counts: dict[str, int] = {}
    for _, rung, _ in rows:
        counts[rung] = counts.get(rung, 0) + 1
    for rung, n in sorted(counts.items()):
        print(f"{n:6d}  {rung}")
    print(f"written: {out}")


if __name__ == "__main__":
    main()
