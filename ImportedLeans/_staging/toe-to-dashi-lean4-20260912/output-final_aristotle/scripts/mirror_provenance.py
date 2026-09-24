#!/usr/bin/env python3
"""Mechanical provenance census for the hand-written Lean mirrors of Agda modules.

For every module under ``Lean/AgdaMirror`` this script

1. reads the module header for the Agda file(s) it claims to mirror
   (the convention is a backticked ``Something.agda`` in the first lines),
2. locates those files in the ``Agda`` tree,
3. extracts the top-level declaration names on both sides, and
4. reports, per mirror, how many Agda names have a name-level correspondent in
   the Lean mirror, and which Agda declarations have none.

**What this does and does not establish.**  A name-level correspondence is
evidence of provenance, not of faithfulness: it does not check that a mirrored
theorem *states* the Agda theorem, and it cannot, since the two languages are
compared here only as text.  Its purpose is to make the mirror layer auditable —
to expose mirrors whose claimed source does not exist, and Agda results that the
mirror silently omits — so that a claim resting on a mirrored Agda statement can
be traced to the declaration it comes from.

Usage:  python3 scripts/mirror_provenance.py [--markdown]
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_MIRROR_DIR = ROOT / "Lean" / "AgdaMirror"
AGDA_DIR = ROOT / "Agda"

LEAN_DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+|partial\s+)*"
    r"(def|theorem|lemma|abbrev|structure|inductive|instance|class)\s+"
    r"([A-Za-z_][A-Za-z0-9_'.!?₀-₉]*)"
)
AGDA_SIG = re.compile(r"^([A-Za-z_][^\s:{}()]*)\s*:(?!:)")
AGDA_DATA = re.compile(r"^(?:data|record)\s+([A-Za-z_][^\s:{}()]*)")
AGDA_DEF = re.compile(r"^([A-Za-z_][^\s:{}()=]*)\s*=")
SOURCE_REF = re.compile(r"`([A-Za-z0-9_./-]+\.agda)`")


def normalise(name: str) -> str:
    """Compare names modulo case, hyphens, dots and underscores."""
    return re.sub(r"[^a-z0-9]", "", name.lower())


def lean_declarations(path: Path) -> list[str]:
    names: list[str] = []
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        m = LEAN_DECL.match(line)
        if m:
            names.append(m.group(2).split(".")[-1])
    return names


def agda_declarations(path: Path) -> list[str]:
    names: list[str] = []
    for line in path.read_text(encoding="utf-8", errors="replace").splitlines():
        if line.startswith((" ", "\t", "--", "{-", "module", "open", "import", "infix")):
            continue
        for rx in (AGDA_DATA, AGDA_SIG, AGDA_DEF):
            m = rx.match(line)
            if m:
                names.append(m.group(1))
                break
    # keep first occurrence order, drop duplicates
    seen: set[str] = set()
    out: list[str] = []
    for n in names:
        if n not in seen:
            seen.add(n)
            out.append(n)
    return out


def claimed_sources(path: Path) -> list[str]:
    head = "\n".join(path.read_text(encoding="utf-8", errors="replace").splitlines()[:40])
    return list(dict.fromkeys(SOURCE_REF.findall(head)))


def find_agda(name: str, index: dict[str, list[Path]]) -> list[Path]:
    return index.get(Path(name).name, [])


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--markdown", action="store_true", help="emit a markdown table")
    args = parser.parse_args()

    index: dict[str, list[Path]] = {}
    for p in AGDA_DIR.rglob("*.agda"):
        index.setdefault(p.name, []).append(p)

    rows = []
    for lean in sorted(LEAN_MIRROR_DIR.rglob("*.lean")):
        lean_names = {normalise(n) for n in lean_declarations(lean)}
        sources = claimed_sources(lean)
        if not sources:
            rows.append((lean, None, None, 0, 0, []))
            continue
        for src in sources:
            hits = find_agda(src, index)
            if not hits:
                rows.append((lean, src, None, 0, 0, []))
                continue
            agda = hits[0]
            agda_names = agda_declarations(agda)
            matched = [n for n in agda_names if normalise(n) in lean_names]
            missing = [n for n in agda_names if normalise(n) not in lean_names]
            rows.append((lean, src, agda, len(agda_names), len(matched), missing))

    total = len(rows)
    dangling = [r for r in rows if r[1] is not None and r[2] is None]
    unattributed = [r for r in rows if r[1] is None]
    resolved = [r for r in rows if r[2] is not None]
    decls = sum(r[3] for r in resolved)
    hits = sum(r[4] for r in resolved)

    if args.markdown:
        print("| Lean mirror | claimed Agda source | Agda decls | name-matched | unmatched |")
        print("| --- | --- | ---: | ---: | --- |")
        for lean, src, agda, n, m, missing in rows:
            rel = lean.relative_to(ROOT)
            if src is None:
                print(f"| `{rel}` | *(none declared)* | – | – | – |")
            elif agda is None:
                print(f"| `{rel}` | `{src}` **(not in tree)** | – | – | – |")
            else:
                show = ", ".join(f"`{x}`" for x in missing[:6])
                if len(missing) > 6:
                    show += f", … (+{len(missing) - 6})"
                print(f"| `{rel}` | `{agda.relative_to(ROOT)}` | {n} | {m} | {show or '—'} |")
        print()
    print(f"pairs examined              : {total}")
    print(f"  resolved to an Agda file  : {len(resolved)}")
    print(f"  claimed source not found  : {len(dangling)}")
    print(f"  no source declared        : {len(unattributed)}")
    print(f"Agda declarations in scope  : {decls}")
    print(f"  with a name-level match   : {hits}")
    if decls:
        print(f"  coverage                  : {100.0 * hits / decls:.1f}%")
    print()
    print("Name-level correspondence is provenance evidence only; it is not a proof")
    print("that a mirrored statement is faithful to the Agda statement.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
