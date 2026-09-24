#!/usr/bin/env python3
"""Post-intake frontier and cross-pollination analysis of the DASHI Agda corpus.

Reads the tree under ``Agda/`` (post-intake) plus ``XPOLL_LEDGER.csv`` (what this
round adopted) and emits:

  XPOLL_FRONTIER.csv    per newly adopted module: dependency status and the
                        exact missing import edges (direct and inherited)
  XPOLL_HUBS.csv        modules imported from three or more different lanes,
                        i.e. the corpus's actual cross-lane kernels
  XPOLL_SHARED.csv      top-level declaration names that occur in three or more
                        different lanes: shared vocabulary and duplicate-kernel
                        candidates
  XPOLL_FRONTIER.json   aggregate counts

No Agda toolchain exists here; every statement produced is a text-level
import/declaration fact, never a typecheck.

Usage: python3 scripts/xpoll_frontier.py [project-root]
"""

from __future__ import annotations

import collections
import csv
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from xpoll_index import analyse  # noqa: E402


def lane_of(mod: str) -> str:
    parts = mod.split(".")
    return parts[1] if len(parts) > 2 else "(root)"


def main() -> int:
    project = sys.argv[1] if len(sys.argv) > 1 else "."
    agda = os.path.join(project, "Agda")

    imports: dict[str, list[str]] = {}
    decls: dict[str, list[str]] = {}
    for base, _dirs, files in os.walk(agda):
        for f in files:
            if not f.endswith(".agda"):
                continue
            rel = os.path.relpath(os.path.join(base, f), agda)
            mod = rel[:-5].replace(os.sep, ".")
            with open(os.path.join(base, f), encoding="utf-8", errors="replace") as fh:
                info = analyse(fh.read())
            imports[mod] = [i for i in info["imports"] if i.startswith("DASHI.")]
            decls[mod] = info["decls"]

    present = set(imports)
    direct_missing = {m: sorted({d for d in ds if d not in present}) for m, ds in imports.items()}
    incomplete = {m for m, ms in direct_missing.items() if ms}
    changed = True
    while changed:
        changed = False
        for m, ds in imports.items():
            if m in incomplete:
                continue
            if any(d in incomplete for d in ds):
                incomplete.add(m)
                changed = True

    # which modules did this round add?
    added = []
    ledger = os.path.join(project, "XPOLL_LEDGER.csv")
    with open(ledger, encoding="utf-8") as fh:
        for row in csv.DictReader(fh):
            if row["action"] == "new" and row["path"].startswith("Agda/") and row["path"].endswith(".agda"):
                added.append(row["path"][len("Agda/"):-5].replace("/", "."))

    rows = []
    for m in sorted(added):
        blockers = sorted({d for d in imports.get(m, []) if d in incomplete or d not in present})
        rows.append(
            dict(
                module=m,
                lane=lane_of(m),
                status="dependency-complete" if m not in incomplete else "dependency-incomplete",
                direct_missing=";".join(direct_missing.get(m, [])),
                incomplete_dependencies=";".join(b for b in blockers if b in present),
            )
        )
    with open(os.path.join(project, "XPOLL_FRONTIER.csv"), "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    # cross-lane hubs
    # Aggregates import whole lanes by construction, so counting them as
    # importers would make every module look cross-lane.  They are excluded.
    def is_aggregate(mod: str) -> bool:
        return "Everything" in mod.split(".")[-1]

    importers = collections.defaultdict(set)
    for m, ds in imports.items():
        if is_aggregate(m):
            continue
        for d in ds:
            importers[d].add(lane_of(m))
    hubs = sorted(
        ((len(v), d, sorted(v)) for d, v in importers.items() if len(v) >= 3),
        reverse=True,
    )
    with open(os.path.join(project, "XPOLL_HUBS.csv"), "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["module", "importing_lanes", "present", "lanes"])
        for n, d, lanes in hubs:
            w.writerow([d, n, "yes" if d in present else "no", ";".join(lanes)])

    # shared declaration names across lanes
    declared = collections.defaultdict(set)
    for m, ns in decls.items():
        for n in ns:
            declared[n].add(lane_of(m))
    shared = sorted(
        ((len(v), n, sorted(v)) for n, v in declared.items() if len(v) >= 3), reverse=True
    )
    with open(os.path.join(project, "XPOLL_SHARED.csv"), "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["declaration", "lanes", "lane_list"])
        for n, name, lanes in shared[:2000]:
            w.writerow([name, n, ";".join(lanes)])

    summary = dict(
        modules=len(imports),
        dependency_incomplete=len(incomplete),
        modules_with_direct_missing=sum(1 for v in direct_missing.values() if v),
        missing_targets=len({d for v in direct_missing.values() for d in v}),
        adopted_new=len(added),
        adopted_new_complete=sum(1 for r in rows if r["status"] == "dependency-complete"),
        adopted_new_incomplete=sum(1 for r in rows if r["status"] == "dependency-incomplete"),
        cross_lane_hubs=len(hubs),
        shared_declaration_names=len(shared),
    )
    with open(os.path.join(project, "XPOLL_FRONTIER.json"), "w", encoding="utf-8") as fh:
        json.dump(summary, fh, indent=2, sort_keys=True)
    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
