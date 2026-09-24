#!/usr/bin/env python3
"""Post-intake dependency frontier for the local Lean and Agda trees.

For every source file under ``Agda/`` and ``Lean/`` this resolves every
internal import against the module universe actually present in the tree, and
reports the imported-but-absent module names with their importers, plus the
transitively dependency-incomplete modules.

Outputs: SPINE_FRONTIER_POST.csv, SPINE_FRONTIER_POST.json

Usage: python3 scripts/spine_frontier_post.py [project-root]
"""

from __future__ import annotations

import csv
import json
import os
import re
import sys
from collections import defaultdict

AGDA_IMPORT = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z0-9_.\u2032'-]+)")
LEAN_IMPORT = re.compile(r"^\s*import\s+([A-Za-z0-9_.\u00c0-\uffff']+)")
LEAN_EXTERNAL_ROOTS = {"Mathlib", "Std", "Init", "Lean", "Batteries", "Aesop", "Qq", "Plausible",
                       "ImportGraph", "ProofWidgets", "Cli", "LeanSearchClient", "Duper"}


def modules(root: str, ext: str) -> dict[str, str]:
    out = {}
    for base, _dirs, files in os.walk(root):
        for f in files:
            if f.endswith(ext):
                rel = os.path.relpath(os.path.join(base, f), root).replace(os.sep, "/")
                out[rel[: -len(ext)].replace("/", ".")] = rel
    return out


def main() -> int:
    project = sys.argv[1] if len(sys.argv) > 1 else "."
    rows = []
    summary = {}
    for lang, root, ext, imp_re, is_internal in (
        ("agda", os.path.join(project, "Agda"), ".agda", AGDA_IMPORT,
         lambda i: i.startswith("DASHI.")),
        ("lean", os.path.join(project, "Lean"), ".lean", LEAN_IMPORT,
         lambda i: i.split(".")[0] not in LEAN_EXTERNAL_ROOTS),
    ):
        mods = modules(root, ext)
        # A second, more generous resolution: the corpus contains several
        # package roots (`Lean/DASHI/output-final_aristotle`, the Klüver
        # package, the vendored `ImportedLeans` checkouts), so a module may be
        # present under a different source root.  `suffix` resolution accepts
        # any file whose path ends with the module's path.
        suffixes = {p for p in mods.values()}
        suffix_index = set()
        for p in suffixes:
            parts = p.split("/")
            for i in range(len(parts)):
                suffix_index.add(".".join(parts[i:])[: -len(ext)] if i == 0 else
                                 ".".join(parts[i:])[: -len(ext)])
        deps: dict[str, list[str]] = {}
        missing = defaultdict(list)
        missing_even_by_suffix = defaultdict(list)
        edges = internal_edges = 0
        for mod, rel in sorted(mods.items()):
            with open(os.path.join(root, rel), encoding="utf-8", errors="replace") as fh:
                imps = [m.group(1) for m in (imp_re.match(l) for l in fh) if m]
            edges += len(imps)
            ints = [i for i in imps if is_internal(i)]
            internal_edges += len(ints)
            deps[mod] = ints
            for i in ints:
                if i not in mods:
                    missing[i].append(mod)
                    if i not in suffix_index:
                        missing_even_by_suffix[i].append(mod)
        incomplete = {m for m, ds in deps.items() if any(d not in mods for d in ds)}
        changed = True
        while changed:
            changed = False
            for m, ds in deps.items():
                if m not in incomplete and any(d in incomplete for d in ds):
                    incomplete.add(m)
                    changed = True
        for t, importers in sorted(missing.items()):
            rows.append(dict(lang=lang, missing_module=t, importer_count=len(set(importers)),
                             resolution="absent-from-tree" if t in missing_even_by_suffix
                             else "present-under-another-source-root",
                             importers=";".join(sorted(set(importers))[:25])))
        summary[lang] = dict(files=len(mods), import_edges=edges, internal_edges=internal_edges,
                             unresolved_edges=sum(len(v) for v in missing.values()),
                             unresolved_targets=len(missing),
                             files_with_unresolved=len({m for v in missing.values() for m in v}),
                             absent_from_tree_targets=len(missing_even_by_suffix),
                             absent_from_tree_edges=sum(len(v) for v in missing_even_by_suffix.values()),
                             dependency_incomplete=len(incomplete))
    with open(os.path.join(project, "SPINE_FRONTIER_POST.csv"), "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=["lang", "missing_module", "importer_count",
                                           "resolution", "importers"])
        w.writeheader()
        w.writerows(rows)
    with open(os.path.join(project, "SPINE_FRONTIER_POST.json"), "w", encoding="utf-8") as fh:
        json.dump(summary, fh, indent=2, sort_keys=True)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
