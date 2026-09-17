#!/usr/bin/env python3
"""Generate the `AgdaCheck` library: one Lean module per ingested Agda module,
each of which does nothing but hand the *raw* `.agda` file to the Lean front end
of `RequestProject.Agda.Verbatim`.

`tools/agda2lean.py` rewrites Agda into the `agda_module` front end offline and
checks the result in under `AgdaVendor/`.  `AgdaCheck` is the same corpus taken
the other way: Lean reads the upstream source itself, at elaboration time, with
no pre-pass at all.  Building `AgdaCheck` is therefore a machine-checked
measurement of how much of the corpus Lean can interpret directly as sugar.

A module is *attempted* when

  * the Lean front end normalises and parses it — which is decided by the front
    end itself, not by a mirror of its rules written here: the report
    `docs/AGDA_FRONTEND_PARSE.txt`, produced by `tools/AgdaParse.lean`, says
    which files pass,
  * every Agda module it imports is either supplied by the prelude or attempted
    itself,
  * and it is not listed in `tools/agdacheck_skipped.txt`, which records the
    modules that pass the syntactic gate but do not elaborate — each with the
    reason, so the gap is documented rather than hidden.

Usage
-----

    lake env lean tools/AgdaParse.lean > docs/AGDA_FRONTEND_PARSE.txt
    python3 tools/agdacheck.py --emit      # write the AgdaCheck modules
    python3 tools/agdacheck.py --report    # coverage of the direct route
"""

from __future__ import annotations

import argparse
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import agda2lean as A  # noqa: E402

ROOT = A.ROOT
OUTDIR = os.path.join(ROOT, "AgdaCheck")
SKIP = os.path.join(ROOT, "tools", "agdacheck_skipped.txt")
PARSE = os.path.join(ROOT, "docs", "AGDA_FRONTEND_PARSE.txt")

MIXFIX_RE = re.compile(r"^_(\S+)_$")


def deps_of(body: list[str]) -> list[str]:
    """The Agda modules a body imports, in any of the forms the front end reads:
    `import M`, `import M as A`, `open import M …`."""
    ds = []
    for line in body:
        m = re.match(r"^(?:open\s+)?import\s+(\S+)", line.strip())
        if m:
            ds.append(m.group(1))
    return ds


def parse_report() -> dict[str, str | None]:
    """`{path: None if the front end reads it else reason}`, from the report the
    front end itself writes."""
    if not os.path.exists(PARSE):
        sys.exit(f"{PARSE} is missing; regenerate it with\n"
                 "  lake env lean tools/AgdaParse.lean > docs/AGDA_FRONTEND_PARSE.txt")
    out: dict[str, str | None] = {}
    for line in open(PARSE, encoding="utf-8"):
        line = line.rstrip("\n")
        if line.startswith("ok   "):
            out[os.path.join(ROOT, line[5:].strip())] = None
        elif line.startswith("skip "):
            rest = line[5:]
            path, _, why = rest.partition("   [")
            out[os.path.join(ROOT, path.strip())] = why.rstrip("]") or "outside the fragment"
    return out


def verbatim_reasons(path: str, gate: dict[str, str | None]) -> \
        tuple[str, list[str], list[str]]:
    """The module's name, why the front end will not read it (empty if it will),
    and what it imports.  The verdict comes from `gate`, which is the front
    end's own report."""
    lines = open(path, encoding="utf-8").read().split("\n")
    body: list[str] = []
    header = None
    for i, l in enumerate(lines):
        if l.startswith("module "):
            header = l
            body = lines[i + 1:]
            break
    if header is None:
        return "", ["no module header"], []
    toks = header.split()
    if len(toks) != 3 or toks[2] != "where":
        return "", ["parametrised or malformed module header"], []
    module = toks[1]
    why = gate.get(os.path.abspath(path), "not in the front end's report")
    return module, ([] if why is None else [why]), deps_of(body)


def unique_corpus(gate: dict[str, str | None] | None = None) -> list[str]:
    """One file per Agda module.  Where a module occurs on several upstream
    branches, the copy the front end can read wins, and otherwise the branch
    order below decides."""
    files = A.corpus_files()
    priority = ["agent/evidence-polarity-cross-pollination",
                "agent/progenitor-parent-hyperfabric", "master"]

    def rank(path: str) -> int:
        rel = os.path.relpath(path, A.CORPUS)
        for i, b in enumerate(priority):
            if rel.startswith(b + os.sep):
                return i
        return len(priority)

    def reads(path: str) -> int:
        if gate is None:
            return 0
        return 0 if gate.get(os.path.abspath(path), "") is None else 1

    files = sorted(files, key=lambda f: (A.module_of(f), reads(f), rank(f)))
    seen: set[str] = set()
    unique = []
    for f in files:
        m = A.module_of(f)
        if m in seen:
            continue
        seen.add(m)
        unique.append(f)
    return unique


def load_skipped() -> dict[str, str]:
    """`{module: reason}` from `tools/agdacheck_skipped.txt`: the modules that
    pass the syntactic gate but do not elaborate."""
    skipped: dict[str, str] = {}
    if os.path.exists(SKIP):
        for line in open(SKIP, encoding="utf-8"):
            line = line.rstrip()
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            name, _, why = line.partition("#")
            skipped[name.strip()] = why.strip()
    return skipped


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--emit", action="store_true")
    ap.add_argument("--report", action="store_true")
    args = ap.parse_args()

    skipped = load_skipped()

    gate = parse_report()
    info: dict[str, tuple[list[str], list[str], str]] = {}
    for f in unique_corpus(gate):
        module, rs, deps = verbatim_reasons(f, gate)
        if not module:
            continue
        deps = [d for d in deps if not d.startswith(A.PRELUDE_PREFIXES)]
        info[module] = (rs, deps, f)

    ok = {m: not v[0] and m not in skipped for m, v in info.items()}
    for m, (rs, deps, _f) in info.items():
        for d in deps:
            if d not in info:
                rs.append(f"dependency outside the ingested corpus: {d}")
                ok[m] = False
    changed = True
    while changed:
        changed = False
        for m, (rs, deps, _f) in info.items():
            if not ok[m]:
                continue
            for d in deps:
                if not ok.get(d, False):
                    rs.append(f"dependency not attempted: {d}")
                    ok[m] = False
                    changed = True
                    break

    attempted = sorted(m for m in info if ok[m])

    if args.report:
        print(f"corpus: {len(info)} Agda modules under upstream/dashi_agda")
        print(f"read directly by the Lean front end: {len(attempted)}")
        counts: dict[str, int] = {}
        for m, (rs, _d, _f) in info.items():
            if ok[m]:
                continue
            key = (skipped[m] or "does not elaborate") if m in skipped \
                else (sorted(set(rs))[0].split(":")[0] if rs else "unknown")
            counts[key] = counts.get(key, 0) + 1
        print("not attempted, by first reason:")
        for k, v in sorted(counts.items(), key=lambda kv: -kv[1]):
            print(f"  {v:4d}  {k}")
        print()
        for m in sorted(info):
            if ok[m]:
                print(f"ok    {m}")
            else:
                why = skipped.get(m) if m in skipped else "; ".join(sorted(set(info[m][0])))
                print(f"skip  {m}   [{why}]")

    if args.emit:
        for base, _dirs, names in os.walk(OUTDIR):
            for n in names:
                if n.endswith(".lean"):
                    os.remove(os.path.join(base, n))
        for m in attempted:
            _rs, deps, path = info[m]
            rel = os.path.relpath(path, ROOT)
            lines = ["import RequestProject.Agda.Verbatim"]
            for d in sorted(set(deps)):
                lines.append(f"import AgdaCheck.{d}")
            lines += [
                "",
                "/-!",
                f"# `{m}`, read directly from Agda",
                "",
                "This module contains no hand-written Lean.  It hands the upstream Agda",
                f"source `{rel}` to the Lean front end, which normalises and elaborates it",
                "at build time; Lean's kernel then checks the declarations it produces.",
                "",
                "Generated by `tools/agdacheck.py`; do not edit by hand.",
                "-/",
                "",
                f'agda_include "{rel}"',
                "",
            ]
            dest = os.path.join(OUTDIR, *m.split(".")) + ".lean"
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            with open(dest, "w", encoding="utf-8") as fh:
                fh.write("\n".join(lines))
        print(f"wrote {len(attempted)} Lean modules under AgdaCheck")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
