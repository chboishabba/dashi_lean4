#!/usr/bin/env python3
"""Declarations shared across three or more lanes, over the post-intake tree.

Two tables are produced.

* Agda: lane = the ``DASHI/<lane>`` directory.  Aggregate/``Everything`` modules
  are excluded (they re-export, they do not declare).
* Lean: lane = the owning library / package area, restricted to the *first
  party* areas (the six declared libraries and the two `DASHI/*` packages).
  The vendored mirror corpora (`ImportedLeans/`, `Imported/`, `outputs/`) are
  excluded: they are byte-level copies of each other and of the first-party
  files, so counting them would report copying as sharing.  A separate column
  records how many vendored copies each name also has.

Output: SPINE_SHARED_DECLS_FOCUSED.csv

Usage: python3 scripts/spine_shared_decls.py [project-root]
"""

from __future__ import annotations

import csv
import os
import re
import sys
from collections import defaultdict

AGDA_TOPLEVEL = re.compile(r"^([A-Za-z_][A-Za-z0-9_'\u2032-]*)\s*:(?!=)")
LEAN_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|scoped\s+|noncomputable\s+|partial\s+|unsafe\s+|nonrec\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|instance|class)\b\s*([A-Za-z_][A-Za-z0-9_'.!?]*)"
)
LEAN_FIRST_PARTY = ("Synthesis", "Spine", "Integration", "Promoted", "Cuisine", "AgdaMirror", "DASHI")
VENDORED = ("ImportedLeans", "Imported", "outputs")
GENERIC = {"one", "two", "three", "half", "map", "step", "act", "dot", "pow", "pow2", "sym",
           "cong", "trans", "append", "iterate", "square", "main", "run", "fields", "about",
           "hello", "this", "to", "is", "bases", "Not", "State", "Path", "Order", "Vector"}


def main() -> int:
    project = sys.argv[1] if len(sys.argv) > 1 else "."
    rows = []

    # --- Agda -------------------------------------------------------------
    lanes = defaultdict(set)
    paths = defaultdict(list)
    root = os.path.join(project, "Agda")
    for base, _d, files in os.walk(root):
        for f in files:
            if not f.endswith(".agda"):
                continue
            rel = os.path.relpath(os.path.join(base, f), root).replace(os.sep, "/")
            parts = rel.split("/")
            if parts[0] != "DASHI" or len(parts) < 3:
                continue
            if "Everything" in f or f == "All.agda":
                continue
            lane = parts[1]
            with open(os.path.join(base, f), encoding="utf-8", errors="replace") as fh:
                for line in fh:
                    m = AGDA_TOPLEVEL.match(line)
                    if m:
                        lanes[m.group(1)].add(lane)
                        paths[m.group(1)].append(rel)
    for name, ls in lanes.items():
        if len(ls) >= 3 and name not in GENERIC:
            rows.append(dict(lang="agda", declaration=name, lane_count=len(ls),
                             lanes=";".join(sorted(ls)), occurrences=len(paths[name]),
                             vendored_copies=0, example=paths[name][0]))

    # --- Lean -------------------------------------------------------------
    lanes = defaultdict(set)
    paths = defaultdict(list)
    vendored = defaultdict(int)
    root = os.path.join(project, "Lean")
    for base, _d, files in os.walk(root):
        for f in files:
            if not f.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(base, f), root).replace(os.sep, "/")
            top = rel.split("/")[0]
            with open(os.path.join(base, f), encoding="utf-8", errors="replace") as fh:
                names = [m.group(2) for m in (LEAN_DECL.match(l) for l in fh) if m]
            if top in VENDORED:
                for n in set(names):
                    vendored[n] += 1
                continue
            if top not in LEAN_FIRST_PARTY:
                continue
            lane = ("DASHI/" + rel.split("/")[1]) if top == "DASHI" else top
            for n in names:
                lanes[n].add(lane)
                paths[n].append(rel)
    for name, ls in lanes.items():
        if len(ls) >= 3 and name not in GENERIC:
            rows.append(dict(lang="lean", declaration=name, lane_count=len(ls),
                             lanes=";".join(sorted(ls)), occurrences=len(paths[name]),
                             vendored_copies=vendored.get(name, 0), example=paths[name][0]))

    rows.sort(key=lambda r: (r["lang"], -r["lane_count"], -r["occurrences"], r["declaration"]))
    with open(os.path.join(project, "SPINE_SHARED_DECLS_FOCUSED.csv"), "w", newline="",
              encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=["lang", "declaration", "lane_count", "lanes",
                                           "occurrences", "vendored_copies", "example"])
        w.writeheader()
        w.writerows(rows)
    for lang in ("agda", "lean"):
        rr = [r for r in rows if r["lang"] == lang]
        print(lang, len(rr))
        for r in rr[:30]:
            print(f"  {r['declaration'][:46]:48s} {r['lane_count']:>2} lanes  occ={r['occurrences']:>4}"
                  f"  vend={r['vendored_copies']:>4}  {r['lanes'][:80]}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
