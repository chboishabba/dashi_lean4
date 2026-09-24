#!/usr/bin/env python3
"""Cross-reference the OpenAI NS/Euler tranche against the DASHI corpus.

Reads the artefacts produced by `ns_openai_index.py` plus the existing
`SPINE_INDEX.csv`, and indexes the DASHI-side Lean surfaces directly.

Emits:

  NS_DASHI_LEAN_DECLS.csv    declarations of the first-party DASHI Lean surfaces
  NS_LINEAGE_SHARED.csv      declaration base-names present on both sides
  NS_AGDA_NS_LANE.csv        per-file profile of the Agda NS closure lane
  NS_LINEAGE_SUMMARY.json    roll-up counts used by the report

Pure source analysis.  No Lean or Agda kernel is invoked.
"""

from __future__ import annotations

import csv
import hashlib
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ns_openai_index import analyse, sha256, strip_block_comments  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# First-party DASHI Lean surfaces (the vendored `Lean/ImportedLeans` provenance
# corpus is deliberately excluded: it is outside every build target and is
# indexed already by SPINE_INDEX.csv).
DASHI_LEAN_ROOTS = [
    "Lean/Spine",
    "Lean/Synthesis",
    "Lean/Promoted",
    "Lean/Integration",
    "Lean/Cuisine",
    "Lean/Proposed",
    "Lean/AgdaMirror",
    "Provenance/ns_worker_result",
]
DASHI_LEAN_SINGLE = [
    "Lean/NavierStokesClosure.lean",
    "Lean/ClosureEndToEnd.lean",
    "Lean/SpectralClosure.lean",
    "Lean/MoonshineFractran.lean",
]

AGDA_NS_PREFIX = "DASHI/Physics/Closure/"

AGDA_DECL_RE = re.compile(r"^([A-Za-z_][^\s:]*)\s*:")
AGDA_IMPORT_RE = re.compile(r"^(?:open\s+)?import\s+(\S+)")


def index_dashi_lean():
    rows = []
    files = []
    for rel in DASHI_LEAN_SINGLE:
        full = os.path.join(ROOT, rel)
        if os.path.isfile(full):
            files.append((full, rel))
    for root in DASHI_LEAN_ROOTS:
        base = os.path.join(ROOT, root)
        if not os.path.isdir(base):
            continue
        for dirpath, _d, filenames in os.walk(base):
            for fn in sorted(filenames):
                if fn.endswith(".lean"):
                    full = os.path.join(dirpath, fn)
                    files.append((full, os.path.relpath(full, ROOT).replace(os.sep, "/")))
    files.sort(key=lambda t: t[1])

    for full, rel in files:
        info = analyse(full, rel)
        digest = sha256(full)
        for lineno, kind, name, ns, mods in info["decls"]:
            rows.append({
                "path": rel,
                "sha256": digest,
                "line": lineno,
                "kind": kind,
                "name": name,
                "namespace": ns,
                "fully_qualified": (ns + "." + name) if ns else name,
                "modifiers": mods,
            })
    return files, rows


def index_agda_ns_lane():
    rows = []
    base = os.path.join(ROOT, "Agda", AGDA_NS_PREFIX)
    if not os.path.isdir(base):
        return rows
    agda_files = []
    for dirpath, _d, filenames in os.walk(base):
        for fn in sorted(filenames):
            if fn.endswith(".agda"):
                agda_files.append(os.path.join(dirpath, fn))
    for full in sorted(agda_files):
        rel = os.path.relpath(full, base).replace(os.sep, "/")
        fn = rel
        with open(full, encoding="utf-8", errors="replace") as fh:
            text = fh.read()
        lines = text.splitlines()
        imports = [m.group(1) for line in lines for m in [AGDA_IMPORT_RE.match(line.strip())] if m]
        decls = [m.group(1) for line in lines
                 for m in [AGDA_DECL_RE.match(line)] if m]
        rows.append({
            "path": ("Agda/" + AGDA_NS_PREFIX + fn),
            "module": "DASHI.Physics.Closure." + fn[: -len(".agda")].replace("/", "."),
            "sha256": sha256(full),
            "lines": len(lines),
            "imports": len(imports),
            "top_level_decls": len(decls),
            "postulate": len(re.findall(r"^\s*postulate\b", text, re.M)),
            "holes": text.count("{!"),
            "bool_ledger": len(re.findall(r":\s*Bool\s*$", text, re.M)),
            "refl_pins": len(re.findall(r"=\s*refl\s*$", text, re.M)),
            "absurd_boundary": text.count("→ ⊥"),
            "round": (re.search(r"Round(\d+)", fn).group(1) if re.search(r"Round(\d+)", fn) else ""),
        })
    return rows


GENERIC = {
    "ext", "mk", "rfl", "aux", "main", "run", "eval", "toString", "instance",
}


def main() -> int:
    lean_files, dashi_decls = index_dashi_lean()
    agda_rows = index_agda_ns_lane()

    with open(os.path.join(ROOT, "NS_DASHI_LEAN_DECLS.csv"), "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(dashi_decls[0].keys()))
        w.writeheader()
        w.writerows(dashi_decls)

    if agda_rows:
        with open(os.path.join(ROOT, "NS_AGDA_NS_LANE.csv"), "w", newline="", encoding="utf-8") as fh:
            w = csv.DictWriter(fh, fieldnames=list(agda_rows[0].keys()))
            w.writeheader()
            w.writerows(agda_rows)

    # ---- shared base names, upstream vs DASHI Lean ----
    up = {}
    for r in csv.DictReader(open(os.path.join(ROOT, "NS_OPENAI_DECLS.csv"), encoding="utf-8")):
        up.setdefault(r["name"], []).append(r["fully_qualified"] + " @" + r["module"])
    dn = {}
    for r in dashi_decls:
        dn.setdefault(r["name"], []).append(r["fully_qualified"] + " @" + r["path"])

    shared = []
    for name in sorted(set(up) & set(dn)):
        if name in GENERIC or len(name) < 4:
            continue
        shared.append({
            "name": name,
            "n_openai": len(up[name]),
            "n_dashi_lean": len(dn[name]),
            "openai_examples": " | ".join(up[name][:3]),
            "dashi_examples": " | ".join(dn[name][:3]),
        })
    with open(os.path.join(ROOT, "NS_LINEAGE_SHARED.csv"), "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=["name", "n_openai", "n_dashi_lean",
                                           "openai_examples", "dashi_examples"])
        w.writeheader()
        w.writerows(shared)

    summary = {
        "dashi_lean_files_indexed": len(lean_files),
        "dashi_lean_declarations": len(dashi_decls),
        "agda_ns_closure_lane_files": len(agda_rows),
        "agda_ns_closure_lane_lines": sum(r["lines"] for r in agda_rows),
        "agda_ns_closure_lane_decls": sum(r["top_level_decls"] for r in agda_rows),
        "agda_ns_closure_lane_postulates": sum(r["postulate"] for r in agda_rows),
        "agda_ns_closure_lane_holes": sum(r["holes"] for r in agda_rows),
        "agda_ns_closure_lane_bool_ledger": sum(r["bool_ledger"] for r in agda_rows),
        "agda_ns_closure_lane_refl_pins": sum(r["refl_pins"] for r in agda_rows),
        "shared_declaration_basenames_openai_vs_dashi_lean": len(shared),
        "shared_names": [s["name"] for s in shared],
    }
    with open(os.path.join(ROOT, "NS_LINEAGE_SUMMARY.json"), "w", encoding="utf-8") as fh:
        json.dump(summary, fh, indent=2)
        fh.write("\n")
    print(json.dumps(summary, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
