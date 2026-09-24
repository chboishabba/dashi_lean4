#!/usr/bin/env python3
"""Compute the Agda import/dependency provenance graph for the DASHI corpus.

Excludes the vendored `Agda/cubical` standard library and any Yang-Mills /
Navier-Stokes material.  Emits a domain-level cross-import matrix, hub
statistics, and the modules that mention each of the integration junctions.
"""
from __future__ import annotations
import os, re, json, sys, collections

ROOT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "Agda")
EXCLUDE_DIR_PARTS = {"cubical"}
EXCLUDE_NAME_RE = re.compile(r"YangMills|NavierStokes|Navier_Stokes|YM_", re.I)

IMPORT_RE = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z0-9_.'\u00c0-\uffff]+)")


def module_name(path: str) -> str:
    rel = os.path.relpath(path, ROOT)
    rel = rel[: -len(".agda")]
    return rel.replace(os.sep, ".")


def collect():
    mods = {}
    for dirpath, dirnames, filenames in os.walk(ROOT):
        parts = set(os.path.relpath(dirpath, ROOT).split(os.sep))
        if parts & EXCLUDE_DIR_PARTS:
            dirnames[:] = []
            continue
        for fn in filenames:
            if not fn.endswith(".agda"):
                continue
            p = os.path.join(dirpath, fn)
            if EXCLUDE_NAME_RE.search(p):
                continue
            name = module_name(p)
            try:
                with open(p, encoding="utf-8", errors="replace") as fh:
                    text = fh.read()
            except OSError:
                continue
            imps = []
            for line in text.splitlines():
                m = IMPORT_RE.match(line)
                if m:
                    imps.append(m.group(1))
            mods[name] = {
                "path": os.path.relpath(p, os.path.dirname(ROOT)),
                "imports": imps,
                "lines": text.count("\n") + 1,
                "text": text,
            }
    return mods


def domain_of(name: str) -> str:
    parts = name.split(".")
    if parts[0] == "DASHI":
        if len(parts) >= 3:
            return "DASHI." + parts[1]
        return "DASHI.<root>"
    if parts[0] in ("Monster", "MDL"):
        return parts[0]
    return "<top-level>"


def main():
    mods = collect()
    names = set(mods)
    dom_edges = collections.Counter()
    intra = collections.Counter()
    indeg = collections.Counter()
    for n, d in mods.items():
        dn = domain_of(n)
        for i in d["imports"]:
            if i not in names:
                continue
            indeg[i] += 1
            di = domain_of(i)
            if di == dn:
                intra[dn] += 1
            else:
                dom_edges[(dn, di)] += 1
    domains = collections.Counter(domain_of(n) for n in mods)

    out = {
        "n_modules": len(mods),
        "n_lines": sum(d["lines"] for d in mods.values()),
        "domains": domains.most_common(),
        "intra_edges": intra.most_common(),
        "cross_edges": [(a, b, c) for (a, b), c in dom_edges.most_common()],
        "top_imported": indeg.most_common(40),
    }
    junctions = {
        "Trit": re.compile(r"\bTrit\b"),
        "Base369": re.compile(r"Base369"),
        "Hyperfabric": re.compile(r"[Hh]yperfabric"),
        "Codec": re.compile(r"[Cc]odec"),
        "Supervoxel": re.compile(r"[Ss]upervoxel"),
        "Clopen": re.compile(r"[Cc]lopen"),
        "Loom": re.compile(r"[Ll]oom"),
        "Monster": re.compile(r"Monster"),
        "Moonshine": re.compile(r"[Mm]oonshine"),
        "Mask": re.compile(r"[Mm]askSign|MaskLayer|\bMask\b"),
        "Fifteen": re.compile(r"\b15\b|[Ff]ifteen"),
    }
    jstats = {}
    for k, rx in junctions.items():
        hits = [n for n, d in mods.items() if rx.search(d["text"])]
        jstats[k] = {
            "count": len(hits),
            "by_domain": collections.Counter(domain_of(h) for h in hits).most_common(12),
        }
    out["junctions"] = jstats
    json.dump(out, sys.stdout, indent=1, ensure_ascii=False)


if __name__ == "__main__":
    main()
