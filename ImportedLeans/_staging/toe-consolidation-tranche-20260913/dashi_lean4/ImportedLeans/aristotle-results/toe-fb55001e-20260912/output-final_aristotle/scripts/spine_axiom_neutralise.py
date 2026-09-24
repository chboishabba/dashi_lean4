#!/usr/bin/env python3
"""Comment out `axiom` declarations in Lean sources adopted from a donor tranche.

The 2026-09-10 tranche's vendored `Lean/ImportedLeans/` corpus is provenance
material, not a proof library: it is outside every `lean_lib` glob and is never
built.  It nonetheless contains `axiom` declarations, and this project's
soundness policy forbids *introducing* `axiom` declarations.  Rather than drop
those files (which would violate the "preserve every source" instruction), each
`axiom` declaration is commented out line-by-line with `-- ` and a marker, so

  * the text is preserved verbatim inside the comment,
  * no axiom is declared,
  * the edit is mechanical, auditable and reversible.

The original bytes remain recoverable: the donor sha256 of every path is in
`SPINE_INDEX.csv` and `SPINE_INTAKE_LEDGER.csv`, and this script writes
`SPINE_AXIOM_NEUTRALISATION.csv` with before/after hashes, the axiom names and
the exact line ranges commented.

Usage: python3 scripts/spine_axiom_neutralise.py <file-list> [project-root] [--apply]
"""

from __future__ import annotations

import csv
import hashlib
import re
import sys

AXIOM_START = re.compile(r"^(\s*)axiom\s+([A-Za-z_][A-Za-z0-9_'.!?]*)")
STOP = re.compile(
    r"^\s*(theorem|lemma|def|abbrev|structure|inductive|instance|class|axiom|opaque|example|"
    r"noncomputable|private|protected|scoped|partial|unsafe|nonrec|open|namespace|end|section|"
    r"variable|universe|import|macro|notation|syntax|deriving|attribute|set_option|@\[|--|/-|#)\b"
)
MARKER = ("-- [spine-intake 2026-09-10] `axiom` declaration commented out on intake: this "
          "vendored provenance file is not built, and the project does not introduce axioms. "
          "Text preserved verbatim below; original sha256 in SPINE_AXIOM_NEUTRALISATION.csv.")


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def neutralise(text: str) -> tuple[str, list[tuple[str, int, int]]]:
    lines = text.split("\n")
    out: list[str] = []
    spans: list[tuple[str, int, int]] = []
    i = 0
    while i < len(lines):
        m = AXIOM_START.match(lines[i])
        if not m:
            out.append(lines[i])
            i += 1
            continue
        start = i
        j = i + 1
        while j < len(lines) and lines[j].strip() != "" and not STOP.match(lines[j]):
            j += 1
        out.append(MARKER)
        for k in range(start, j):
            out.append("-- " + lines[k] if lines[k].strip() else "--")
        spans.append((m.group(2), start + 1, j))
        i = j
    return "\n".join(out), spans


def main() -> int:
    listing = sys.argv[1]
    project = sys.argv[2] if len(sys.argv) > 2 else "."
    apply = "--apply" in sys.argv
    rows = []
    with open(listing, encoding="utf-8") as fh:
        paths = [l.strip() for l in fh if l.strip()]
    for rel in paths:
        full = rel if rel.startswith("/") else f"{project}/{rel}"
        with open(full, "rb") as fh:
            raw = fh.read()
        text = raw.decode("utf-8", errors="replace")
        new, spans = neutralise(text)
        if not spans:
            continue
        nb = new.encode("utf-8")
        if apply:
            with open(full, "wb") as fh:
                fh.write(nb)
        rows.append(dict(path=rel, axioms=len(spans),
                         axiom_names=";".join(n for n, _s, _e in spans),
                         line_ranges=";".join(f"{s}-{e}" for _n, s, e in spans),
                         sha256_before=sha256_bytes(raw), sha256_after=sha256_bytes(nb)))
    with open(f"{project}/SPINE_AXIOM_NEUTRALISATION.csv", "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=["path", "axioms", "axiom_names", "line_ranges",
                                           "sha256_before", "sha256_after"])
        w.writeheader()
        w.writerows(rows)
    print(f"{len(rows)} files, {sum(r['axioms'] for r in rows)} axiom declarations",
          "applied" if apply else "dry-run")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
