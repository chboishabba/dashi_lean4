#!/usr/bin/env python3
"""Index the 2026-09-10 full cross-pollination DASHI Agda source handoff.

Produces, for every donor payload path:
  * sha256, size, line count, declared module name
  * every ``import`` edge (DASHI-internal and external library)
  * mechanical content markers (postulate / TERMINATING / primTrustMe / holes /
    data / record / Bool-ledger obligations / absurdity boundaries)
  * comparison against the local ``Agda/`` tree: absent / identical / divergent
  * for divergent paths, whether the donor preserves every local top-level
    declaration name and every local DASHI import (the reconciliation test)

Outputs (project root):
  XPOLL_INDEX.csv          one row per donor payload path
  XPOLL_IMPORT_EDGES.csv   one row per import edge, with resolution status
  XPOLL_INDEX_SUMMARY.json aggregate counts

Usage: python3 scripts/xpoll_index.py <donor-root> [project-root]
"""

from __future__ import annotations

import csv
import hashlib
import json
import os
import re
import sys

IMPORT_RE = re.compile(r"^\s*(?:open\s+)?import\s+([A-Za-z0-9_.\u2032'-]+)")
MODULE_RE = re.compile(r"^\s*module\s+([A-Za-z0-9_.\u2032'-]+)")
TOPLEVEL_RE = re.compile(r"^([A-Za-z_][A-Za-z0-9_'\u2032-]*)\s*:(?!=)")
DATA_RE = re.compile(r"^\s*data\s+")
RECORD_RE = re.compile(r"^\s*record\s+")
LEDGER_RE = re.compile(r"\u2261\s*true")
ABSURD_RE = re.compile(r"\u2192\s*\u22a5")


def sha256_of(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def analyse(text: str) -> dict:
    imports, decls = [], []
    module = ""
    data = record = postulate = terminating = trustme = holes = 0
    ledger = absurd = 0
    for line in text.splitlines():
        m = IMPORT_RE.match(line)
        if m:
            imports.append(m.group(1))
        if not module:
            mm = MODULE_RE.match(line)
            if mm:
                module = mm.group(1)
        t = TOPLEVEL_RE.match(line)
        if t:
            decls.append(t.group(1))
        if DATA_RE.match(line):
            data += 1
        if RECORD_RE.match(line):
            record += 1
        if re.match(r"^\s*postulate\b", line):
            postulate += 1
        if "TERMINATING" in line or "NON_TERMINATING" in line:
            terminating += 1
        if "primTrustMe" in line or "trustMe" in line:
            trustme += 1
        if re.search(r"(^|\s)\?(\s|$)", line) or "{!" in line:
            holes += 1
        if LEDGER_RE.search(line):
            ledger += 1
        if ABSURD_RE.search(line):
            absurd += 1
    return dict(
        module=module,
        imports=imports,
        decls=decls,
        data=data,
        record=record,
        postulate=postulate,
        terminating=terminating,
        trustme=trustme,
        holes=holes,
        ledger=ledger,
        absurd=absurd,
    )


def main() -> int:
    donor_root = sys.argv[1]
    project = sys.argv[2] if len(sys.argv) > 2 else "."
    payload = os.path.join(donor_root, "dashi_agda")
    local_agda = os.path.join(project, "Agda")

    donor_paths = []
    for base, _dirs, files in os.walk(payload):
        for f in files:
            if f.endswith(".agda"):
                full = os.path.join(base, f)
                donor_paths.append(os.path.relpath(full, payload))
    donor_paths.sort()

    # local module universe (module name -> relative path), for edge resolution
    local_modules = set()
    local_rel = set()
    for base, _dirs, files in os.walk(local_agda):
        for f in files:
            if f.endswith(".agda"):
                rel = os.path.relpath(os.path.join(base, f), local_agda)
                local_rel.add(rel)
                local_modules.add(rel[:-5].replace(os.sep, "."))
    donor_modules = {p[:-5].replace(os.sep, ".") for p in donor_paths}

    rows = []
    edges = []
    infos = {}
    for rel in donor_paths:
        dp = os.path.join(payload, rel)
        with open(dp, encoding="utf-8", errors="replace") as fh:
            text = fh.read()
        info = analyse(text)
        infos[rel] = info
        dsha = sha256_of(dp)
        lp = os.path.join(local_agda, rel)
        if os.path.exists(lp):
            lsha = sha256_of(lp)
            status = "identical" if lsha == dsha else "divergent"
        else:
            lsha = ""
            status = "absent-locally"
        preserves = ""
        if status == "divergent":
            with open(lp, encoding="utf-8", errors="replace") as fh:
                linfo = analyse(fh.read())
            missing_decls = set(linfo["decls"]) - set(info["decls"])
            missing_imports = {i for i in linfo["imports"] if i.startswith("DASHI.")} - set(
                info["imports"]
            )
            preserves = "yes" if not missing_decls and not missing_imports else "no"
            infos[rel]["missing_decls"] = sorted(missing_decls)
            infos[rel]["missing_imports"] = sorted(missing_imports)
        lane = rel.split(os.sep)[1] if rel.count(os.sep) >= 1 else "(root)"
        rows.append(
            dict(
                path=rel.replace(os.sep, "/"),
                lane=lane,
                module=info["module"],
                sha256_donor=dsha,
                sha256_local=lsha,
                status=status,
                donor_preserves_local=preserves,
                bytes=os.path.getsize(dp),
                lines=text.count("\n") + 1,
                imports=len(info["imports"]),
                dashi_imports=sum(1 for i in info["imports"] if i.startswith("DASHI.")),
                decls=len(info["decls"]),
                data=info["data"],
                record=info["record"],
                postulate=info["postulate"],
                terminating=info["terminating"],
                trustme=info["trustme"],
                holes=info["holes"],
                bool_ledger=info["ledger"],
                absurd_boundary=info["absurd"],
            )
        )
        src_mod = rel[:-5].replace(os.sep, ".")
        for imp in info["imports"]:
            if imp.startswith("DASHI."):
                where = (
                    "both"
                    if imp in donor_modules and imp in local_modules
                    else "donor-only"
                    if imp in donor_modules
                    else "local-only"
                    if imp in local_modules
                    else "unresolved"
                )
            else:
                where = "external"
            edges.append(dict(source=src_mod, target=imp, resolution=where))

    # direct-unresolved set, then transitive dependency completeness over donor∪local
    universe = donor_modules | local_modules
    deps = {}
    for rel in donor_paths:
        src = rel[:-5].replace(os.sep, ".")
        deps[src] = [i for i in infos[rel]["imports"] if i.startswith("DASHI.")]
    # local-only modules: parse their imports too, so closure is honest
    for rel in sorted(local_rel - set(donor_paths)):
        src = rel[:-5].replace(os.sep, ".")
        with open(os.path.join(local_agda, rel), encoding="utf-8", errors="replace") as fh:
            deps[src] = [i for i in analyse(fh.read())["imports"] if i.startswith("DASHI.")]

    incomplete = set()
    for m, ds in deps.items():
        if any(d not in universe for d in ds):
            incomplete.add(m)
    changed = True
    while changed:
        changed = False
        for m, ds in deps.items():
            if m in incomplete:
                continue
            if any(d in incomplete for d in ds):
                incomplete.add(m)
                changed = True

    for r in rows:
        mod = r["path"][:-5].replace("/", ".")
        r["dependency_complete"] = "no" if mod in incomplete else "yes"

    out = os.path.join(project, "XPOLL_INDEX.csv")
    with open(out, "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    with open(os.path.join(project, "XPOLL_IMPORT_EDGES.csv"), "w", newline="", encoding="utf-8") as fh:
        w = csv.DictWriter(fh, fieldnames=["source", "target", "resolution"])
        w.writeheader()
        w.writerows(edges)

    unresolved = sorted({e["target"] for e in edges if e["resolution"] == "unresolved"})
    summary = dict(
        donor_files=len(rows),
        identical=sum(1 for r in rows if r["status"] == "identical"),
        absent_locally=sum(1 for r in rows if r["status"] == "absent-locally"),
        divergent=sum(1 for r in rows if r["status"] == "divergent"),
        divergent_donor_preserves=sum(1 for r in rows if r["donor_preserves_local"] == "yes"),
        divergent_donor_drops=sum(1 for r in rows if r["donor_preserves_local"] == "no"),
        local_only=len(local_rel - set(donor_paths)),
        import_edges=len(edges),
        dashi_edges=sum(1 for e in edges if e["resolution"] != "external"),
        unresolved_edges=sum(1 for e in edges if e["resolution"] == "unresolved"),
        unresolved_targets=unresolved,
        dependency_incomplete=sum(1 for r in rows if r["dependency_complete"] == "no"),
        postulate_files=sum(1 for r in rows if r["postulate"]),
        terminating_files=sum(1 for r in rows if r["terminating"]),
        trustme_files=sum(1 for r in rows if r["trustme"]),
        lanes={},
    )
    for r in rows:
        summary["lanes"][r["lane"]] = summary["lanes"].get(r["lane"], 0) + 1
    with open(os.path.join(project, "XPOLL_INDEX_SUMMARY.json"), "w", encoding="utf-8") as fh:
        json.dump(summary, fh, indent=2, sort_keys=True)

    # divergence detail
    with open(os.path.join(project, "XPOLL_DIVERGENCES.csv"), "w", newline="", encoding="utf-8") as fh:
        w = csv.writer(fh)
        w.writerow(["path", "donor_preserves_local", "local_decls_dropped", "local_dashi_imports_dropped"])
        for rel in donor_paths:
            i = infos[rel]
            if "missing_decls" in i:
                w.writerow(
                    [
                        rel.replace(os.sep, "/"),
                        "yes" if not i["missing_decls"] and not i["missing_imports"] else "no",
                        ";".join(i["missing_decls"]),
                        ";".join(i["missing_imports"]),
                    ]
                )

    print(json.dumps({k: v for k, v in summary.items() if k != "unresolved_targets"}, indent=2))
    print("unresolved targets:", len(unresolved))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
