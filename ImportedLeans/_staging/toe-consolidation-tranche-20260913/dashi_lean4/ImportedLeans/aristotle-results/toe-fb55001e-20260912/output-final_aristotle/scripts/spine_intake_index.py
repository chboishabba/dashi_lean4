#!/usr/bin/env python3
"""Index the 2026-09-10 combined Lean + Agda consolidation tranche.

The tranche ships two payload roots:

  ``dashi_lean4/``  -> local ``Lean/``   (donor commit c5b9a072…)
  ``dashi_agda/``   -> local ``Agda/``   (donor commit a866c675…)

For every delivered path this script records

  * sha256 (donor and local), size, line count, language, lane
  * the declared module / namespace and every top-level declaration name
  * every ``import`` edge with a resolution status against donor ∪ local
  * mechanical content markers
      Agda: data / record / postulate / TERMINATING / primTrustMe / holes /
            ``≡ true`` Boolean-ledger obligations / ``→ ⊥`` boundaries
      Lean: theorem / def / structure / instance counts, ``sorry``, ``axiom``,
            ``native_decide``, ``@[implemented_by]``, ``partial``
  * the comparison against the local tree: identical / divergent / absent
  * for divergent paths, whether the donor version preserves every local
    top-level declaration name and every local internal import (the
    reconciliation test that decides adopt-donor vs keep-local)

Outputs, at the project root:

  SPINE_INDEX.csv           one row per delivered payload path
  SPINE_IMPORT_EDGES.csv    one row per import edge
  SPINE_DIVERGENCES.csv     divergent paths with the declarations at stake
  SPINE_FRONTIER.csv        imported-but-absent module names, with importers
  SPINE_SHARED_DECLS.csv    declaration names shared across >= 3 lanes
  SPINE_INDEX_SUMMARY.json  aggregate counts

Usage: python3 scripts/spine_intake_index.py <tranche-root> [project-root]
"""

from __future__ import annotations

import csv
import hashlib
import json
import os
import re
import sys
from collections import defaultdict

AGDA_IMPORT = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z0-9_.\u2032'-]+)")
AGDA_MODULE = re.compile(r"^\s*module\s+([A-Za-z0-9_.\u2032'-]+)")
AGDA_TOPLEVEL = re.compile(r"^([A-Za-z_][A-Za-z0-9_'\u2032-]*)\s*:(?!=)")
LEDGER_RE = re.compile(r"\u2261\s*true")
ABSURD_RE = re.compile(r"\u2192\s*\u22a5")

LEAN_IMPORT = re.compile(r"^\s*import\s+([A-Za-z0-9_.\u00c0-\uffff']+)")
LEAN_NAMESPACE = re.compile(r"^\s*namespace\s+([A-Za-z0-9_.\u00c0-\uffff']+)")
LEAN_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|scoped\s+|noncomputable\s+|partial\s+|unsafe\s+|nonrec\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|instance|class|axiom|opaque|example)\b\s*([^\s({\[:⦃]*)"
)
LEAN_EXTERNAL_ROOTS = {"Mathlib", "Std", "Init", "Lean", "Batteries", "Aesop", "Qq", "Plausible",
                       "ImportGraph", "ProofWidgets", "Cli", "LeanSearchClient", "Duper"}


def sha256_of(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def analyse_agda(text: str) -> dict:
    imports, decls = [], []
    module = ""
    counts = defaultdict(int)
    for line in text.splitlines():
        m = AGDA_IMPORT.match(line)
        if m:
            imports.append(m.group(1))
        if not module:
            mm = AGDA_MODULE.match(line)
            if mm:
                module = mm.group(1)
        t = AGDA_TOPLEVEL.match(line)
        if t:
            decls.append(t.group(1))
        if re.match(r"^\s*data\s+", line):
            counts["data"] += 1
        if re.match(r"^\s*record\s+", line):
            counts["record"] += 1
        if re.match(r"^\s*postulate\b", line):
            counts["postulate"] += 1
        if "TERMINATING" in line:
            counts["terminating"] += 1
        if "primTrustMe" in line or "trustMe" in line:
            counts["trustme"] += 1
        if re.search(r"(^|\s)\?(\s|$)", line) or "{!" in line:
            counts["holes"] += 1
        if LEDGER_RE.search(line):
            counts["bool_ledger"] += 1
        if ABSURD_RE.search(line):
            counts["absurd_boundary"] += 1
    return dict(module=module, imports=imports, decls=decls, counts=dict(counts))


def analyse_lean(text: str) -> dict:
    imports, decls = [], []
    namespaces: list[str] = []
    counts = defaultdict(int)
    for line in text.splitlines():
        m = LEAN_IMPORT.match(line)
        if m:
            imports.append(m.group(1))
        n = LEAN_NAMESPACE.match(line)
        if n:
            namespaces.append(n.group(1))
        d = LEAN_DECL.match(line)
        if d:
            kind, name = d.group(1), d.group(2)
            counts[kind] += 1
            if name:
                decls.append(name)
        if re.search(r"\bsorry\b", line):
            counts["sorry"] += 1
        if re.match(r"^\s*axiom\b", line):
            counts["axiom_decl"] += 1
        if "native_decide" in line:
            counts["native_decide"] += 1
        if "implemented_by" in line:
            counts["implemented_by"] += 1
        if re.match(r"^\s*partial\b", line):
            counts["partial"] += 1
    return dict(module="/".join(namespaces[:1]), imports=imports, decls=decls,
                counts=dict(counts), namespaces=namespaces)


def lane_of(lang: str, rel: str) -> str:
    parts = rel.split("/")
    if lang == "agda":
        return parts[1] if len(parts) >= 2 and parts[0] == "DASHI" else (parts[0] if len(parts) > 1 else "(root)")
    if len(parts) == 1:
        return "(root)"
    if parts[0] == "ImportedLeans":
        return "ImportedLeans/" + (parts[1] if len(parts) > 2 else "(root)")
    if parts[0] == "DASHI":
        return "DASHI/" + parts[1]
    return parts[0]


def collect(root: str, exts: tuple[str, ...]) -> list[str]:
    out = []
    for base, _dirs, files in os.walk(root):
        for f in files:
            full = os.path.join(base, f)
            rel = os.path.relpath(full, root)
            if not exts or rel.endswith(exts):
                out.append(rel.replace(os.sep, "/"))
    out.sort()
    return out


def main() -> int:
    tranche = sys.argv[1]
    project = sys.argv[2] if len(sys.argv) > 2 else "."

    langs = [
        ("agda", os.path.join(tranche, "dashi_agda"), os.path.join(project, "Agda"), (".agda",)),
        ("lean", os.path.join(tranche, "dashi_lean4"), os.path.join(project, "Lean"), (".lean",)),
    ]

    # module universes ------------------------------------------------------
    universe = {}
    donor_mods = {}
    local_mods = {}
    for lang, dpayload, lroot, exts in langs:
        dm = {p[: -len(exts[0])].replace("/", ".") for p in collect(dpayload, exts)}
        lm = {p[: -len(exts[0])].replace("/", ".") for p in collect(lroot, exts)} if os.path.isdir(lroot) else set()
        donor_mods[lang], local_mods[lang] = dm, lm
        universe[lang] = dm | lm

    rows, edges, divergences = [], [], []
    frontier = defaultdict(list)
    decl_lanes = defaultdict(set)
    decl_paths = defaultdict(list)

    for lang, dpayload, lroot, exts in langs:
        for rel in collect(dpayload, ()):  # every delivered file, not only sources
            dp = os.path.join(dpayload, rel)
            lp = os.path.join(lroot, rel)
            dsha = sha256_of(dp)
            if os.path.exists(lp):
                lsha = sha256_of(lp)
                status = "identical" if lsha == dsha else "divergent"
            else:
                lsha, status = "", "absent-locally"
            is_source = rel.endswith(exts[0])
            info = dict(module="", imports=[], decls=[], counts={})
            text = ""
            if is_source:
                with open(dp, encoding="utf-8", errors="replace") as fh:
                    text = fh.read()
                info = analyse_agda(text) if lang == "agda" else analyse_lean(text)
            lane = lane_of(lang, rel)
            preserves = ""
            if status == "divergent":
                if is_source:
                    with open(lp, encoding="utf-8", errors="replace") as fh:
                        linfo = analyse_agda(fh.read()) if lang == "agda" else analyse_lean(fh.read())
                    dropped = sorted(set(linfo["decls"]) - set(info["decls"]))
                    internal = (lambda i: i.startswith("DASHI.")) if lang == "agda" else (
                        lambda i: i.split(".")[0] not in LEAN_EXTERNAL_ROOTS)
                    dropped_imports = sorted({i for i in linfo["imports"] if internal(i)} - set(info["imports"]))
                    preserves = "yes" if not dropped and not dropped_imports else "no"
                else:
                    dropped, dropped_imports = [], []
                    preserves = "n/a-nonsource"
                divergences.append(dict(lang=lang, path=rel, lane=lane,
                                        sha256_donor=dsha, sha256_local=lsha,
                                        donor_preserves_local=preserves,
                                        local_decls_dropped=";".join(dropped),
                                        local_imports_dropped=";".join(dropped_imports)))
            src_mod = rel[: -len(exts[0])].replace("/", ".") if is_source else ""
            for imp in info["imports"]:
                if lang == "agda":
                    internal = imp.startswith("DASHI.")
                else:
                    internal = imp.split(".")[0] not in LEAN_EXTERNAL_ROOTS
                if not internal:
                    res = "external"
                elif imp in donor_mods[lang] and imp in local_mods[lang]:
                    res = "both"
                elif imp in donor_mods[lang]:
                    res = "donor-only"
                elif imp in local_mods[lang]:
                    res = "local-only"
                else:
                    res = "unresolved"
                    frontier[(lang, imp)].append(src_mod)
                edges.append(dict(lang=lang, source=src_mod, target=imp, resolution=res))
            for d in info["decls"]:
                decl_lanes[(lang, d)].add(lane)
                decl_paths[(lang, d)].append(rel)
            c = info["counts"]
            rows.append(dict(
                lang=lang, path=rel, lane=lane, module=src_mod,
                sha256_donor=dsha, sha256_local=lsha, status=status,
                donor_preserves_local=preserves,
                bytes=os.path.getsize(dp), lines=(text.count("\n") + 1) if text else 0,
                imports=len(info["imports"]),
                internal_imports=sum(1 for i in info["imports"]
                                     if (i.startswith("DASHI.") if lang == "agda"
                                         else i.split(".")[0] not in LEAN_EXTERNAL_ROOTS)),
                decls=len(info["decls"]),
                data=c.get("data", 0), record=c.get("record", 0),
                postulate=c.get("postulate", 0), terminating=c.get("terminating", 0),
                trustme=c.get("trustme", 0), holes=c.get("holes", 0),
                bool_ledger=c.get("bool_ledger", 0), absurd_boundary=c.get("absurd_boundary", 0),
                theorem=c.get("theorem", 0) + c.get("lemma", 0), definition=c.get("def", 0) + c.get("abbrev", 0),
                structure=c.get("structure", 0) + c.get("inductive", 0) + c.get("class", 0),
                instance=c.get("instance", 0),
                sorry=c.get("sorry", 0), axiom_decl=c.get("axiom_decl", 0),
                native_decide=c.get("native_decide", 0), implemented_by=c.get("implemented_by", 0),
            ))

    # transitive dependency completeness over donor ∪ local -----------------
    for lang, dpayload, lroot, exts in langs:
        deps: dict[str, list[str]] = {}
        internal = (lambda i: i.startswith("DASHI.")) if lang == "agda" else (
            lambda i: i.split(".")[0] not in LEAN_EXTERNAL_ROOTS)
        for rel in collect(dpayload, exts):
            with open(os.path.join(dpayload, rel), encoding="utf-8", errors="replace") as fh:
                info = analyse_agda(fh.read()) if lang == "agda" else analyse_lean(fh.read())
            deps[rel[: -len(exts[0])].replace("/", ".")] = [i for i in info["imports"] if internal(i)]
        if os.path.isdir(lroot):
            for rel in collect(lroot, exts):
                mod = rel[: -len(exts[0])].replace("/", ".")
                if mod in deps:
                    continue
                with open(os.path.join(lroot, rel), encoding="utf-8", errors="replace") as fh:
                    info = analyse_agda(fh.read()) if lang == "agda" else analyse_lean(fh.read())
                deps[mod] = [i for i in info["imports"] if internal(i)]
        incomplete = {m for m, ds in deps.items() if any(d not in universe[lang] for d in ds)}
        changed = True
        while changed:
            changed = False
            for m, ds in deps.items():
                if m not in incomplete and any(d in incomplete for d in ds):
                    incomplete.add(m)
                    changed = True
        for r in rows:
            if r["lang"] == lang and r["module"]:
                r["dependency_complete"] = "no" if r["module"] in incomplete else "yes"
    for r in rows:
        r.setdefault("dependency_complete", "n/a")

    def dump(name, fieldnames, data):
        with open(os.path.join(project, name), "w", newline="", encoding="utf-8") as fh:
            w = csv.DictWriter(fh, fieldnames=fieldnames)
            w.writeheader()
            w.writerows(data)

    dump("SPINE_INDEX.csv", list(rows[0].keys()), rows)
    dump("SPINE_IMPORT_EDGES.csv", ["lang", "source", "target", "resolution"], edges)
    dump("SPINE_DIVERGENCES.csv",
         ["lang", "path", "lane", "sha256_donor", "sha256_local", "donor_preserves_local",
          "local_decls_dropped", "local_imports_dropped"], divergences)

    frows = [dict(lang=lang, missing_module=t, importer_count=len(set(v)),
                  importers=";".join(sorted(set(v))[:20]))
             for (lang, t), v in sorted(frontier.items())]
    dump("SPINE_FRONTIER.csv", ["lang", "missing_module", "importer_count", "importers"], frows)

    srows = []
    for (lang, d), lanes in sorted(decl_lanes.items()):
        if len(lanes) >= 3:
            srows.append(dict(lang=lang, declaration=d, lane_count=len(lanes),
                              lanes=";".join(sorted(lanes)),
                              occurrences=len(decl_paths[(lang, d)])))
    srows.sort(key=lambda r: (-r["lane_count"], r["declaration"]))
    dump("SPINE_SHARED_DECLS.csv", ["lang", "declaration", "lane_count", "lanes", "occurrences"], srows)

    summary = {}
    for lang, *_ in langs:
        lr = [r for r in rows if r["lang"] == lang]
        summary[lang] = dict(
            delivered=len(lr),
            identical=sum(1 for r in lr if r["status"] == "identical"),
            divergent=sum(1 for r in lr if r["status"] == "divergent"),
            absent_locally=sum(1 for r in lr if r["status"] == "absent-locally"),
            donor_preserves_local=sum(1 for r in lr if r["donor_preserves_local"] == "yes"),
            donor_drops_local=sum(1 for r in lr if r["donor_preserves_local"] == "no"),
            declarations=sum(r["decls"] for r in lr),
            import_edges=sum(1 for e in edges if e["lang"] == lang),
            unresolved_edges=sum(1 for e in edges if e["lang"] == lang and e["resolution"] == "unresolved"),
            unresolved_targets=sum(1 for (l, _t) in frontier if l == lang),
            dependency_incomplete=sum(1 for r in lr if r["dependency_complete"] == "no"),
            postulate_files=sum(1 for r in lr if r["postulate"]),
            sorry_files=sum(1 for r in lr if r["sorry"]),
            axiom_files=sum(1 for r in lr if r["axiom_decl"]),
            native_decide_files=sum(1 for r in lr if r["native_decide"]),
            bool_ledger_files=sum(1 for r in lr if r["bool_ledger"]),
        )
    summary["shared_decls_ge3_lanes"] = len(srows)
    summary["lanes"] = {}
    for r in rows:
        key = f"{r['lang']}:{r['lane']}"
        summary["lanes"][key] = summary["lanes"].get(key, 0) + 1
    with open(os.path.join(project, "SPINE_INDEX_SUMMARY.json"), "w", encoding="utf-8") as fh:
        json.dump(summary, fh, indent=2, sort_keys=True)
    print(json.dumps({k: v for k, v in summary.items() if k != "lanes"}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
