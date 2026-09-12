#!/usr/bin/env python3
"""Index the OpenAI NavierStokesAndEuler Lean tranche (pinned f9e8bc5b...).

Emits, into the project root:

  NS_OPENAI_INDEX.csv         one row per delivered file
  NS_OPENAI_DECLS.csv         one row per top-level declaration
  NS_OPENAI_IMPORT_EDGES.csv  one row per `import` line, with resolution
  NS_OPENAI_INDEX_SUMMARY.json

Idempotent: regenerating overwrites the four artefacts and nothing else.
Pure source analysis -- no Lean elaboration is performed or implied.
"""

from __future__ import annotations

import csv
import hashlib
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TRANCHE = os.path.join(ROOT, "Provenance", "openai-ns-20260912")
REPO = os.path.join(TRANCHE, "openai_NavierStokesAndEuler")

DECL_KINDS = (
    "theorem", "lemma", "def", "abbrev", "structure", "class", "instance",
    "inductive", "example", "opaque", "axiom", "macro", "notation",
)

# A top-level declaration begins in column 0, optionally behind modifiers.
MODIFIERS = r"(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|nonrec\s+|noncomputable\s+|unsafe\s+|partial\s+|scoped\s+|local\s+)*"
DECL_RE = re.compile(
    r"^(?P<mods>" + MODIFIERS + r")(?P<kind>" + "|".join(DECL_KINDS) + r")\b[ \t]*(?P<name>[^\s:({\[⦃⟨]*)"
)
IMPORT_RE = re.compile(r"^import\s+([A-Za-z_][A-Za-z0-9_.'\u2080-\u2089]*)")
NS_RE = re.compile(r"^namespace\s+(\S+)")
END_RE = re.compile(r"^end\s+(\S+)")


def sha256(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def module_of(relpath: str) -> str:
    assert relpath.endswith(".lean")
    return relpath[: -len(".lean")].replace(os.sep, ".")


def strip_block_comments(lines):
    """Return lines with /- ... -/ regions blanked, preserving line count."""
    out = []
    depth = 0
    for line in lines:
        buf = []
        i = 0
        while i < len(line):
            if depth == 0 and line.startswith("/-", i):
                depth += 1
                i += 2
            elif depth > 0 and line.startswith("/-", i):
                depth += 1
                i += 2
            elif depth > 0 and line.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if depth == 0:
                    buf.append(line[i])
                i += 1
        out.append("".join(buf))
    return out


def analyse(path: str, relpath: str):
    with open(path, encoding="utf-8", errors="replace") as fh:
        raw = fh.read()
    lines = raw.splitlines()
    code = strip_block_comments(lines)

    imports = []
    decls = []
    ns_stack = []
    for lineno, (rawline, codeline) in enumerate(zip(lines, code), start=1):
        m = IMPORT_RE.match(rawline.strip()) if rawline.startswith("import") else None
        if m:
            imports.append((lineno, m.group(1)))
            continue
        s = codeline
        if not s.strip():
            continue
        mn = NS_RE.match(s)
        if mn:
            ns_stack.append(mn.group(1))
            continue
        me = END_RE.match(s)
        if me:
            if ns_stack and ns_stack[-1] == me.group(1):
                ns_stack.pop()
            continue
        if s[0] in " \t":
            continue
        md = DECL_RE.match(s)
        if md and md.group("name"):
            name = md.group("name")
            if name in ("where", "extends", ":=", "by"):
                continue
            decls.append(
                (lineno, md.group("kind"), name, ".".join(ns_stack), md.group("mods").strip())
            )

    # sorry / axiom accounting on comment-stripped code
    codetext = "\n".join(code)
    sorries = len(re.findall(r"\bsorry\b", codetext))
    admits = len(re.findall(r"\badmit\b", codetext))
    axioms = len(re.findall(r"^axiom\b", codetext, re.M))
    natdec = len(re.findall(r"\bnative_decide\b", codetext))
    printax = re.findall(r"^#print axioms\s+(\S+)", codetext, re.M)

    return {
        "lines": len(lines),
        "bytes": len(raw.encode("utf-8")),
        "imports": imports,
        "decls": decls,
        "sorry": sorries,
        "admit": admits,
        "axiom": axioms,
        "native_decide": natdec,
        "print_axioms": printax,
    }


def main() -> int:
    if not os.path.isdir(REPO):
        print("missing tranche at %s" % REPO, file=sys.stderr)
        return 2

    lean_files = []
    for dirpath, _dirnames, filenames in os.walk(REPO):
        for fn in sorted(filenames):
            if fn.endswith(".lean"):
                full = os.path.join(dirpath, fn)
                lean_files.append((full, os.path.relpath(full, REPO)))
    lean_files.sort(key=lambda t: t[1])

    modules = {module_of(rel) for _f, rel in lean_files}

    idx_rows = []
    decl_rows = []
    edge_rows = []
    summary = {
        "tranche": "openai-ns-20260912",
        "upstream_repo": "https://github.com/openai/NavierStokesAndEuler",
        "upstream_commit": "f9e8bc5b38b6e212696e8a30e3e91517af887bbd",
        "lean_files": len(lean_files),
    }

    kind_counts = {}
    lane_counts = {}
    total_lines = 0
    total_decls = 0
    total_sorry = 0
    total_axiom = 0

    for full, rel in lean_files:
        info = analyse(full, rel)
        mod = module_of(rel)
        lane = rel.split(os.sep)[0] if os.sep in rel else "(root)"
        lane_counts[lane] = lane_counts.get(lane, 0) + 1
        total_lines += info["lines"]
        total_decls += len(info["decls"])
        total_sorry += info["sorry"]
        total_axiom += info["axiom"]

        idx_rows.append({
            "path": os.path.join("Provenance/openai-ns-20260912/openai_NavierStokesAndEuler", rel).replace(os.sep, "/"),
            "module": mod,
            "lane": lane,
            "sha256": sha256(full),
            "lines": info["lines"],
            "bytes": info["bytes"],
            "n_imports": len(info["imports"]),
            "n_decls": len(info["decls"]),
            "n_theorems": sum(1 for d in info["decls"] if d[1] in ("theorem", "lemma")),
            "n_defs": sum(1 for d in info["decls"] if d[1] in ("def", "abbrev", "opaque")),
            "n_structures": sum(1 for d in info["decls"] if d[1] in ("structure", "class", "inductive")),
            "sorry": info["sorry"],
            "admit": info["admit"],
            "axiom_decls": info["axiom"],
            "native_decide": info["native_decide"],
            "print_axioms": ";".join(info["print_axioms"]),
        })

        for lineno, kind, name, ns, mods in info["decls"]:
            kind_counts[kind] = kind_counts.get(kind, 0) + 1
            fq = (ns + "." + name) if ns else name
            decl_rows.append({
                "module": mod,
                "lane": lane,
                "line": lineno,
                "kind": kind,
                "name": name,
                "namespace": ns,
                "fully_qualified": fq,
                "modifiers": mods,
            })

        for lineno, target in info["imports"]:
            if target in modules:
                res = "in-tranche"
            elif target == "Mathlib" or target.startswith("Mathlib."):
                res = "mathlib"
            elif target.startswith("Comparator"):
                res = "comparator-pkg"
            elif target.startswith("Lean") or target.startswith("Init") or target.startswith("Std"):
                res = "core"
            else:
                res = "unresolved"
            edge_rows.append({
                "source_module": mod,
                "line": lineno,
                "target_module": target,
                "resolution": res,
            })

    def write_csv(name, rows, fields):
        with open(os.path.join(ROOT, name), "w", newline="", encoding="utf-8") as fh:
            w = csv.DictWriter(fh, fieldnames=fields)
            w.writeheader()
            for r in rows:
                w.writerow(r)

    write_csv("NS_OPENAI_INDEX.csv", idx_rows, list(idx_rows[0].keys()))
    write_csv("NS_OPENAI_DECLS.csv", decl_rows, list(decl_rows[0].keys()))
    write_csv("NS_OPENAI_IMPORT_EDGES.csv", edge_rows, list(edge_rows[0].keys()))

    res_counts = {}
    for e in edge_rows:
        res_counts[e["resolution"]] = res_counts.get(e["resolution"], 0) + 1

    summary.update({
        "total_lines": total_lines,
        "total_declarations": total_decls,
        "declaration_kinds": dict(sorted(kind_counts.items(), key=lambda kv: -kv[1])),
        "files_per_lane": lane_counts,
        "total_sorry_tokens": total_sorry,
        "total_axiom_declarations": total_axiom,
        "import_edges": len(edge_rows),
        "import_resolution": res_counts,
        "unresolved_targets": sorted({e["target_module"] for e in edge_rows if e["resolution"] == "unresolved"}),
    })
    with open(os.path.join(ROOT, "NS_OPENAI_INDEX_SUMMARY.json"), "w", encoding="utf-8") as fh:
        json.dump(summary, fh, indent=2, sort_keys=False)
        fh.write("\n")

    print(json.dumps({k: v for k, v in summary.items() if k != "unresolved_targets"}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
