#!/usr/bin/env python3
"""Index the 2026-09-12 "latest NS Aristotle source tranche" and place it in the
public-proof lineage.

Inputs (all inside this repository, nothing is downloaded):

  ns-latest-source-tranche-to-toe-20260912.tar.gz   the delivered archive
  Provenance/ns-latest-20260912/SOURCE_MANIFEST.txt the delivered manifest
  Provenance/ns-latest-20260912/SHA256SUMS          the delivered checksums
  Provenance/ns-latest-20260912/payload/**          the preserved NS subset
  NS_OPENAI_DECLS.csv                               public forced-blowup corpus
  NS_DASHI_LEAN_DECLS.csv                           first-party DASHI Lean decls

Outputs, into the project root:

  NS_LATEST_INDEX.csv        one row per preserved payload file
  NS_LATEST_DECLS.csv        one row per top-level Lean declaration preserved
  NS_LATEST_IMPORT_EDGES.csv one row per `import` line of the preserved Lean
  NS_LATEST_DELTA.csv        one row per delivered file: its status against this
                             repository (identical / differs / absent)
  NS_LATEST_LINEAGE.csv      declaration-name overlap of the four new NS modules
                             against the public corpus and the DASHI Lean corpus
  NS_LATEST_SUMMARY.json     the counts quoted in NS_LATEST_TRANCHE_LINEAGE.md

Idempotent: regenerating overwrites these six artefacts and nothing else.
Pure source analysis -- no Lean elaboration is performed or implied.

With --verify-archive the script additionally extracts the tarball into a
temporary directory and checks every one of its 21,730 checksum lines.  Without
it, only the preserved subset is re-verified against the delivered manifest.
"""

from __future__ import annotations

import csv
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TRANCHE = os.path.join(ROOT, "Provenance", "ns-latest-20260912")
PAYLOAD = os.path.join(TRANCHE, "payload")
ARCHIVE = os.path.join(ROOT, "ns-latest-source-tranche-to-toe-20260912.tar.gz")
PREFIX = "output-final_aristotle/"

NEW_MODULES = (
    "RequestProject/NavierStokes/SpineRateBlockAdapter.lean",
    "RequestProject/NavierStokes/GramConsumerFactorisation.lean",
    "RequestProject/NavierStokes/SlotKernelAntiParallel.lean",
    "RequestProject/NavierStokes/RateBlockGramBound.lean",
)

DECL_KINDS = (
    "theorem", "lemma", "def", "abbrev", "structure", "class", "instance",
    "inductive", "example", "opaque", "axiom", "macro", "notation",
)
MODIFIERS = (
    r"(?:@\[[^\]]*\]\s*)*"
    r"(?:private\s+|protected\s+|nonrec\s+|noncomputable\s+|unsafe\s+|partial\s+|scoped\s+|local\s+)*"
)
DECL_RE = re.compile(
    r"^(?P<mods>" + MODIFIERS + r")(?P<kind>" + "|".join(DECL_KINDS)
    + r")\b[ \t]*(?P<name>[^\s:({\[⦃⟨]*)"
)
IMPORT_RE = re.compile(r"^import\s+([A-Za-z_][A-Za-z0-9_.'\u2080-\u2089]*)")
NS_RE = re.compile(r"^namespace\s+(\S+)")
END_RE = re.compile(r"^end\s+(\S+)")


def sha256_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def read_manifest(path: str) -> dict[str, str]:
    out = {}
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            line = line.rstrip("\n")
            if not line:
                continue
            h, p = line.split("  ", 1)
            if p.startswith(PREFIX):
                out[p[len(PREFIX):]] = h
    return out


def strip_block_comments(lines):
    """Return lines with /- ... -/ regions blanked, preserving line count."""
    out = []
    depth = 0
    for line in lines:
        buf = []
        i = 0
        while i < len(line):
            if line.startswith("/-", i):
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


def analyse_lean(path: str):
    with open(path, encoding="utf-8", errors="replace") as fh:
        lines = fh.read().splitlines()
    code = strip_block_comments(lines)
    imports, decls, ns_stack = [], [], []
    for lineno, (rawline, codeline) in enumerate(zip(lines, code), start=1):
        if rawline.startswith("import") and codeline.startswith("import"):
            m = IMPORT_RE.match(codeline.strip())
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
        if md and md.group("name") and md.group("name") not in ("where", "extends", ":=", "by"):
            decls.append((lineno, md.group("kind"), md.group("name"),
                          ".".join(ns_stack), md.group("mods").strip()))
    codetext = "\n".join(code)
    flags = {
        "sorry": len(re.findall(r"\bsorry\b", codetext)),
        "admit": len(re.findall(r"\badmit\b", codetext)),
        "axiom_decls": sum(1 for d in decls if d[1] == "axiom"),
        "native_decide": len(re.findall(r"\bnative_decide\b", codetext)),
        "print_axioms": len(re.findall(r"#print axioms", codetext)),
    }
    return lines, imports, decls, flags


def repo_hashes() -> dict[str, str]:
    out = {}
    for dirpath, dirnames, filenames in os.walk(ROOT):
        dirnames[:] = [d for d in dirnames if d != ".git"]
        for f in filenames:
            p = os.path.join(dirpath, f)
            rel = os.path.relpath(p, ROOT)
            if rel.startswith(os.path.join("Provenance", "ns-latest-20260912")):
                continue
            try:
                out[rel] = sha256_file(p)
            except OSError:
                pass
    return out


def repo_counterpart(rel: str) -> str:
    """Where a delivered path would live in this repository, if anywhere."""
    if rel.startswith("Lean/") or rel.startswith("Provenance/"):
        return rel
    if rel.endswith(".agda") or rel.startswith("DASHI/"):
        return os.path.join("Agda", rel)
    return rel


def verify_archive() -> dict:
    with tempfile.TemporaryDirectory() as td:
        subprocess.run(["tar", "xzf", ARCHIVE, "-C", td], check=True)
        res = subprocess.run(["sha256sum", "-c", "SHA256SUMS"], cwd=td,
                             capture_output=True, text=True)
        ok = sum(1 for line in res.stdout.splitlines() if line.endswith(": OK"))
        bad = [line for line in res.stdout.splitlines() if not line.endswith(": OK")]
        return {"checked": ok + len(bad), "ok": ok, "failed": len(bad),
                "exit": res.returncode}


def main() -> int:
    manifest = read_manifest(os.path.join(TRANCHE, "SOURCE_MANIFEST.txt"))
    summary: dict = {"delivered_files": len(manifest)}

    if "--verify-archive" in sys.argv:
        summary["archive_checksum_verification"] = verify_archive()

    # ---- 1. the preserved subset, re-verified and indexed -------------------
    index_rows, decl_rows, edge_rows = [], [], []
    preserved, mismatches = 0, []
    module_of_preserved = {}
    for dirpath, _, filenames in os.walk(PAYLOAD):
        for f in sorted(filenames):
            p = os.path.join(dirpath, f)
            rel = os.path.relpath(p, PAYLOAD).replace(os.sep, "/")
            preserved += 1
            h = sha256_file(p)
            if manifest.get(rel) != h:
                mismatches.append(rel)
            if rel.endswith(".lean"):
                lines, imports, decls, flags = analyse_lean(p)
                module = rel[: -len(".lean")].replace("/", ".")
                module_of_preserved[module] = rel
                index_rows.append({
                    "path": rel, "module": module, "sha256": h,
                    "lines": len(lines), "bytes": os.path.getsize(p),
                    "n_imports": len(imports), "n_decls": len(decls),
                    "n_theorems": sum(1 for d in decls if d[1] in ("theorem", "lemma")),
                    "n_defs": sum(1 for d in decls if d[1] in ("def", "abbrev")),
                    "n_structures": sum(1 for d in decls if d[1] in ("structure", "class", "inductive")),
                    **flags,
                })
                for lineno, kind, name, nsp, mods in decls:
                    decl_rows.append({
                        "path": rel, "module": module, "line": lineno, "kind": kind,
                        "name": name, "namespace": nsp,
                        "fully_qualified": f"{nsp}.{name}" if nsp else name,
                        "modifiers": mods,
                    })
                for lineno, target in imports:
                    edge_rows.append({
                        "path": rel, "module": module, "line": lineno,
                        "source_tree": ("ns-lane" if rel.startswith("RequestProject/")
                                        else "toe-donor-version" if rel.startswith("Provenance/")
                                        else "other"),
                        "imports": target,
                        "kind": ("ns-lane" if target.startswith("RequestProject.")
                                 else "toe-spine" if target.startswith("Spine.")
                                 else "toe-proposed" if target.startswith("Proposed.")
                                 else "mathlib" if target.startswith("Mathlib")
                                 else "other"),
                    })
            else:
                index_rows.append({
                    "path": rel, "module": "", "sha256": h,
                    "lines": sum(1 for _ in open(p, "rb")),
                    "bytes": os.path.getsize(p), "n_imports": 0, "n_decls": 0,
                    "n_theorems": 0, "n_defs": 0, "n_structures": 0, "sorry": 0,
                    "admit": 0, "axiom_decls": 0, "native_decide": 0, "print_axioms": 0,
                })
    summary["preserved_files"] = preserved
    summary["preserved_manifest_mismatches"] = mismatches

    # resolution of the preserved lane's import edges
    for row in edge_rows:
        target = row["imports"]
        relpath = target.replace(".", "/") + ".lean"
        if relpath in {r["path"] for r in index_rows}:
            row["resolved"] = "preserved-payload"
        elif os.path.exists(os.path.join(ROOT, "Lean", relpath)):
            row["resolved"] = "this-repo-Lean"
        elif target.startswith("Mathlib"):
            row["resolved"] = "mathlib"
        else:
            row["resolved"] = "unresolved"

    # ---- 2. the whole delivery against this repository ----------------------
    repo = repo_hashes()
    by_content = {}
    for rel, h in repo.items():
        by_content.setdefault(h, rel)
    delta_rows = []
    counts = {"identical": 0, "differs": 0, "absent": 0}
    for rel, h in sorted(manifest.items()):
        cp = repo_counterpart(rel)
        if cp in repo:
            status = "identical" if repo[cp] == h else "differs"
        else:
            status = "absent"
        counts[status] += 1
        delta_rows.append({
            "delivered_path": rel, "sha256": h, "repo_path": cp if cp in repo else "",
            "repo_sha256": repo.get(cp, ""), "status": status,
            "same_content_elsewhere": by_content.get(h, "") if status != "identical" else "",
            "preserved_here": "yes" if os.path.exists(os.path.join(PAYLOAD, rel)) else "no",
        })
    summary["delivery_vs_repo"] = counts
    summary["delivered_content_already_in_repo_by_hash"] = sum(
        1 for rel, h in manifest.items() if h in by_content)

    # ---- 3. lineage: the four new modules against the two decl corpora ------
    def load_names(path: str, col: str) -> dict[str, list[str]]:
        out: dict[str, list[str]] = {}
        with open(os.path.join(ROOT, path), encoding="utf-8", newline="") as fh:
            for row in csv.DictReader(fh):
                out.setdefault(row["name"], []).append(row.get(col, ""))
        return out

    openai = load_names("NS_OPENAI_DECLS.csv", "fully_qualified")
    dashi = load_names("NS_DASHI_LEAN_DECLS.csv", "fully_qualified")
    lineage_rows = []
    for rel in NEW_MODULES:
        for d in [r for r in decl_rows if r["path"] == rel]:
            lineage_rows.append({
                "module": d["module"], "kind": d["kind"], "line": d["line"],
                "fully_qualified": d["fully_qualified"],
                "name_in_public_openai_corpus": "yes" if d["name"] in openai else "no",
                "public_openai_examples": " | ".join(openai.get(d["name"], [])[:3]),
                "name_in_dashi_lean_corpus": "yes" if d["name"] in dashi else "no",
                "dashi_examples": " | ".join(dashi.get(d["name"], [])[:3]),
            })
    summary["new_module_declarations"] = len(lineage_rows)
    summary["new_module_names_shared_with_public_corpus"] = sum(
        1 for r in lineage_rows if r["name_in_public_openai_corpus"] == "yes")
    summary["new_module_names_shared_with_dashi_lean"] = sum(
        1 for r in lineage_rows if r["name_in_dashi_lean_corpus"] == "yes")

    # ---- 4. proof-hygiene totals over the preserved Lean ---------------------
    summary["preserved_lean_files"] = sum(1 for r in index_rows if r["module"])
    summary["preserved_lean_lines"] = sum(r["lines"] for r in index_rows if r["module"])
    summary["preserved_lean_declarations"] = len(decl_rows)
    for key in ("sorry", "admit", "axiom_decls", "native_decide"):
        summary[f"preserved_lean_{key}"] = sum(r[key] for r in index_rows)

    # ---- 5. write -----------------------------------------------------------
    def write(name: str, rows: list[dict], fields: list[str]) -> None:
        with open(os.path.join(ROOT, name), "w", encoding="utf-8", newline="") as fh:
            w = csv.DictWriter(fh, fieldnames=fields)
            w.writeheader()
            w.writerows(rows)

    write("NS_LATEST_INDEX.csv", sorted(index_rows, key=lambda r: r["path"]),
          ["path", "module", "sha256", "lines", "bytes", "n_imports", "n_decls",
           "n_theorems", "n_defs", "n_structures", "sorry", "admit", "axiom_decls",
           "native_decide", "print_axioms"])
    write("NS_LATEST_DECLS.csv", decl_rows,
          ["path", "module", "line", "kind", "name", "namespace", "fully_qualified",
           "modifiers"])
    write("NS_LATEST_IMPORT_EDGES.csv", edge_rows,
          ["path", "module", "source_tree", "line", "imports", "kind", "resolved"])
    write("NS_LATEST_DELTA.csv", delta_rows,
          ["delivered_path", "sha256", "repo_path", "repo_sha256", "status",
           "same_content_elsewhere", "preserved_here"])
    write("NS_LATEST_LINEAGE.csv", lineage_rows,
          ["module", "kind", "line", "fully_qualified", "name_in_public_openai_corpus",
           "public_openai_examples", "name_in_dashi_lean_corpus", "dashi_examples"])
    with open(os.path.join(ROOT, "NS_LATEST_SUMMARY.json"), "w", encoding="utf-8") as fh:
        json.dump(summary, fh, indent=2, sort_keys=True)
        fh.write("\n")

    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
