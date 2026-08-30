#!/usr/bin/env python3
"""Mechanical *signature-shape* comparison for the hand-written Lean mirrors.

``scripts/mirror_provenance.py`` matches mirror declarations to their Agda
originals by **name**.  This script goes one step further and compares the two
declarations' *statement shapes*:

* how many explicit arguments the statement quantifies over (leading ``∀`` /
  ``(x : T) →`` groups on the Agda side, leading binders and ``∀`` groups on the
  Lean side, in both cases ignoring implicit ``{…}`` and instance ``[…]``
  binders);
* how many further top-level arrows the body has; and
* what the conclusion's head connective is (equation, negation, iff,
  existential, conjunction/product, disjunction, or none of these).

It also records whether the Agda declaration sits inside a ``postulate`` block,
which is the case a mirror must never silently upgrade to a proved Lean theorem.

**What this establishes, and what it does not.**  Agreement of shapes is
*necessary but not sufficient* for faithfulness: two statements can share this
shape and still say different things, because nothing here compares the actual
terms, and the two languages' libraries are not identified.  Disagreement, on
the other hand, is a positive signal — a mirror whose arity or conclusion head
differs from its Agda original either states something else or restates it in a
deliberately different form, and either way should be read by hand.  The output
is therefore a *review queue*, not a certificate.  A real faithfulness check
needs an Agda toolchain, which is not available in this environment.

Usage:  python3 scripts/mirror_signature_compare.py [--markdown]
"""

from __future__ import annotations

import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
LEAN_MIRROR_DIR = ROOT / "Lean" / "AgdaMirror"
AGDA_DIR = ROOT / "Agda"

SOURCE_REF = re.compile(r"`([A-Za-z0-9_./-]+\.agda)`")
LEAN_DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+|partial\s+)*"
    r"(def|theorem|lemma|abbrev)\s+"
    r"([^\s:({\[]+)"
)
AGDA_SIG = re.compile(r"^(\s*)([A-Za-z_][^\s:{}()]*)\s*:(?!:)\s*(.*)$")

ARROWS = ("→", "->")


SYMBOL_WORDS = {
    "\u2264": "le", "\u2265": "ge", "\u2261": "eq", "\u2260": "ne", "\u2262": "nne",
    "\u21d2": "imp", "\u2192": "to", "\u2194": "iff", "\u00d7": "prod",
    "\u2070": "0", "\u00b9": "1", "\u00b2": "2", "\u00b3": "3", "\u2074": "4",
    "\u2075": "5", "\u2076": "6", "\u2077": "7", "\u2078": "8", "\u2079": "9",
}


def normalise(name: str) -> str:
    """Compare names modulo case and punctuation, but *not* modulo the symbols
    that distinguish sibling declarations (``lcp\u2264len`` vs ``lcp\u2261len``,
    ``rotateTri`` vs ``rotateTri\u00b3``), which are spelled out instead."""
    for sym, word in SYMBOL_WORDS.items():
        name = name.replace(sym, word)
    return re.sub(r"[^a-z0-9]", "", name.lower())


# --------------------------------------------------------------------------
# shape analysis
# --------------------------------------------------------------------------


def split_top_level(text: str, seps: tuple[str, ...]) -> list[str]:
    """Split ``text`` on any of ``seps`` occurring at bracket depth zero."""
    parts: list[str] = []
    depth = 0
    i = 0
    start = 0
    while i < len(text):
        c = text[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0:
            for sep in seps:
                if text.startswith(sep, i):
                    parts.append(text[start:i])
                    i += len(sep)
                    start = i
                    break
            else:
                i += 1
                continue
            continue
        i += 1
    parts.append(text[start:])
    return parts


def count_explicit_binders(prefix: str) -> int:
    """Number of explicitly bound variables in a binder prefix such as
    ``(a b : T) {c : U} [inst : C] ∀ d``.  Implicit and instance binders are not
    counted, since they are inferable and are conventionally elided."""
    n = 0
    i = 0
    while i < len(prefix):
        c = prefix[i]
        if c in "{[":
            close = "}" if c == "{" else "]"
            depth = 0
            while i < len(prefix):
                if prefix[i] in "{[":
                    depth += 1
                elif prefix[i] in "}]":
                    depth -= 1
                    if depth == 0:
                        break
                i += 1
            i += 1
        elif c == "(":
            depth = 0
            start = i
            while i < len(prefix):
                if prefix[i] == "(":
                    depth += 1
                elif prefix[i] == ")":
                    depth -= 1
                    if depth == 0:
                        break
                i += 1
            group = prefix[start + 1 : i]
            names = group.split(":")[0].strip()
            n += len([t for t in names.split() if t not in ("∀", "_")])
            i += 1
        elif c in "∀":
            i += 1
        elif c.isspace():
            i += 1
        else:
            start = i
            while i < len(prefix) and not prefix[i].isspace() and prefix[i] not in "([{":
                i += 1
            tok = prefix[start:i]
            if tok not in ("∀", "_", ":", "→", "->"):
                n += 1
    return n


def strip_leading_foralls(stmt: str) -> tuple[int, str]:
    """Peel leading ``∀ … ,``/``∀ … →`` groups, returning (#bound, rest)."""
    n = 0
    s = stmt.strip()
    while s.startswith("∀"):
        body = s[1:]
        # the group ends at the first top-level ',' (Lean) or '→' (Agda)
        pieces = split_top_level(body, (",", "→", "->"))
        if len(pieces) < 2:
            break
        n += count_explicit_binders(pieces[0])
        consumed = len(pieces[0])
        rest = body[consumed:].lstrip()
        for sep in (",", "→", "->"):
            if rest.startswith(sep):
                rest = rest[len(sep) :]
                break
        s = rest.strip()
    return n, s


def top_level_eq(text: str) -> bool:
    """Is there an equality sign at bracket depth zero?  ``=>``, ``:=``, ``==``,
    ``≤``/``≥`` and ``≠``/``≢`` do not count."""
    depth = 0
    for i, c in enumerate(text):
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        elif depth == 0:
            if c == "≡":
                return True
            if c == "=":
                prev = text[i - 1] if i else ""
                nxt = text[i + 1] if i + 1 < len(text) else ""
                if prev in ":<>!=+-" or nxt in "=>":
                    continue
                return True
    return False


def head_connective(stmt: str) -> str:
    s = stmt.strip()
    if s.startswith("¬"):
        return "neg"
    top = split_top_level(s, ("↔",))
    if len(top) > 1:
        return "iff"
    if top_level_eq(s):
        return "eq"
    if s.startswith("∃") or s.startswith("Σ"):
        return "exists"
    if len(split_top_level(s, ("×", "∧"))) > 1:
        return "and"
    if len(split_top_level(s, ("⊎", "∨"))) > 1:
        return "or"
    if "≢" in s or "≠" in s:
        return "neq"
    return "other"


def shape(binder_prefix: str, statement: str) -> tuple[int, int, str]:
    """(arity, 0, head connective) for a declaration.

    ``binder_prefix`` is the Lean binder text before the top-level ``:`` (empty
    for Agda, whose binders are all part of the type).  Implicit ``{…}`` and
    instance ``⦃…⦄`` / ``[…]`` binders are not counted on either side."""
    n = count_explicit_binders(binder_prefix)
    extra, rest = strip_leading_foralls(statement)
    n += extra
    pieces = split_top_level(rest, ARROWS)
    for piece in pieces[:-1]:
        p = piece.strip()
        if not p:
            continue
        if (p.startswith("{") and p.endswith("}")) or p.startswith("⦃") or (
            p.startswith("[") and p.endswith("]")
        ):
            continue  # implicit / instance binder written as an arrow
        if p.startswith("∀"):
            k, _ = strip_leading_foralls(p + " → _")
            n += k
        elif p.startswith("(") and p.endswith(")") and ":" in p:
            n += count_explicit_binders(p)
        else:
            n += 1
    concl = pieces[-1]
    extra, concl = strip_leading_foralls(concl)
    n += extra
    return n, 0, head_connective(concl)


# --------------------------------------------------------------------------
# extraction
# --------------------------------------------------------------------------


def agda_signatures(path: Path) -> dict[str, tuple[str, bool]]:
    """name -> (type text, is_postulate)."""
    out: dict[str, tuple[str, bool]] = {}
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    postulate_indent: int | None = None
    i = 0
    while i < len(lines):
        line = lines[i]
        stripped = line.strip()
        indent = len(line) - len(line.lstrip())
        if postulate_indent is not None and stripped and indent <= postulate_indent:
            postulate_indent = None
        if stripped.startswith("postulate"):
            postulate_indent = indent
            i += 1
            continue
        m = AGDA_SIG.match(line)
        if m and not stripped.startswith("--"):
            name = m.group(2)
            body = [m.group(3)]
            j = i + 1
            while j < len(lines):
                nxt = lines[j]
                if not nxt.strip():
                    break
                nxt_indent = len(nxt) - len(nxt.lstrip())
                if nxt_indent <= len(m.group(1)):
                    break
                body.append(nxt.strip())
                j += 1
            out.setdefault(name, (" ".join(body).strip(), postulate_indent is not None))
            i = j
            continue
        i += 1
    return out


def lean_signatures(path: Path) -> dict[str, tuple[str, str]]:
    """name -> (binder prefix, statement)."""
    out: dict[str, tuple[str, str]] = {}
    lines = path.read_text(encoding="utf-8", errors="replace").splitlines()
    i = 0
    while i < len(lines):
        m = LEAN_DECL.match(lines[i])
        if not m:
            i += 1
            continue
        chunk = [lines[i][m.end() :]]
        j = i + 1
        while j < len(lines):
            joined = " ".join(chunk)
            if len(split_top_level(joined, (":=",))) > 1:
                break
            if LEAN_DECL.match(lines[j]) or lines[j].startswith("end "):
                break
            if lines[j].lstrip().startswith("|"):
                break
            chunk.append(lines[j].strip())
            j += 1
        text = " ".join(chunk)
        text = split_top_level(text, (":=",))[0].strip()
        pieces = split_top_level(text, (":",))
        if len(pieces) >= 2:
            binders = pieces[0]
            statement = ":".join(pieces[1:])
        else:
            binders, statement = text, ""
        out.setdefault(m.group(2).split(".")[-1], (binders, statement.strip()))
        i = max(j, i + 1)
    return out


def cited_sources(path: Path) -> list[Path]:
    head = "\n".join(path.read_text(encoding="utf-8", errors="replace").splitlines()[:60])
    names = dict.fromkeys(SOURCE_REF.findall(head))
    found: list[Path] = []
    for n in names:
        base = Path(n).name
        hits = list(AGDA_DIR.rglob(base))
        if hits:
            found.append(hits[0])
    return found


# --------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--markdown", action="store_true")
    args = ap.parse_args()

    rows = []
    total = agree = 0
    postulate_pairs = []
    for lean_file in sorted(LEAN_MIRROR_DIR.rglob("*.lean")):
        srcs = cited_sources(lean_file)
        if not srcs:
            continue
        lsigs = lean_signatures(lean_file)
        if not lsigs:
            continue
        lindex = {normalise(k): (k, v) for k, v in lsigs.items()}
        matched = mismatched = 0
        details = []
        for src in srcs:
            for aname, (atype, is_post) in agda_signatures(src).items():
                key = normalise(aname)
                if key not in lindex:
                    continue
                lname, (binders, statement) = lindex[key]
                if not statement:
                    continue
                a_shape = shape("", atype)
                l_shape = shape(binders, statement)
                total += 1
                ok = a_shape[0] == l_shape[0] and a_shape[2] == l_shape[2]
                if ok:
                    agree += 1
                    matched += 1
                else:
                    mismatched += 1
                    details.append((aname, lname, a_shape, l_shape))
                if is_post:
                    postulate_pairs.append((src.name, aname, lean_file.name, lname))
        if matched or mismatched:
            rows.append((lean_file.relative_to(ROOT), matched, mismatched, details))

    if args.markdown:
        print("# Mirror signature-shape comparison\n")
        print(
            "Generated by `scripts/mirror_signature_compare.py`.  For every "
            "name-matched (Agda declaration, Lean mirror declaration) pair this "
            "compares the **arity** (number of explicitly quantified arguments) "
            "and the **head connective** of the conclusion.\n"
        )
        print(
            "Agreement is necessary, not sufficient, for faithfulness: it does "
            "not compare terms, and the two languages' libraries are not "
            "identified here.  Disagreement is the useful signal — each "
            "disagreeing pair either states something different or restates it "
            "in a deliberately different form, and needs a human reading.  A "
            "genuine faithfulness check requires an Agda toolchain, which is not "
            "available in this environment.\n"
        )
        pct = (100.0 * agree / total) if total else 0.0
        print(f"**Totals:** {total} comparable name-matched pairs; "
              f"{agree} agree on both arity and conclusion head ({pct:.1f} %); "
              f"{total - agree} disagree and are listed below.\n")
        print("## Per-mirror summary\n")
        print("| mirror | agree | disagree |")
        print("|---|---:|---:|")
        for path, m, mm, _ in rows:
            print(f"| `{path}` | {m} | {mm} |")
        print("\n## Pairs needing a human reading\n")
        print("| mirror | declaration | Agda (arity, head) | Lean (arity, head) |")
        print("|---|---|---|---|")
        for path, _, _, details in rows:
            for aname, lname, a, l in details:
                label = aname if normalise(aname) == normalise(lname) else f"{aname} / {lname}"
                print(f"| `{path.name}` | `{label}` | ({a[0]}, {a[2]}) | ({l[0]}, {l[2]}) |")
        print("\n## Agda `postulate`s with a name-matched Lean mirror\n")
        if postulate_pairs:
            print("| Agda file | postulate | mirror | Lean declaration |")
            print("|---|---|---|---|")
            for a, an, lf, ln in postulate_pairs:
                print(f"| `{a}` | `{an}` | `{lf}` | `{ln}` |")
            print(
                "\nA postulate mirrored as a *proved* Lean theorem is not an "
                "error — the Lean side may genuinely prove what the Agda side "
                "assumes — but it is exactly the place where the corpus's own "
                "epistemic status and the mirror's differ, so each row here "
                "should be read."
            )
        else:
            print("None: no Agda `postulate` in a cited source has a name-matched "
                  "declaration in its Lean mirror.")
        print("\n## Known limitations, and what the flags mean in practice\n")
        print(
            "* Only *name-matched* pairs are compared, so a mirror declaration "
            "that renames its original is invisible here; `MIRROR_PROVENANCE.md` "
            "lists the unmatched names.\n"
            "* Comparison is textual.  Long or heavily formatted Agda types are "
            "parsed approximately, and one flagged row "
            "(`TrackedSupport.sum15\u2264`, arity 45 vs 15) is a parse artefact of "
            "a 15-argument signature written across many lines, not a "
            "divergence.\n"
            "* A flag is a *review item*, not an error.  Spot checks of the "
            "current list found three kinds: (i) binder-convention differences "
            "(`countNonZeroNat-mono` quantifies `a b` explicitly in Agda and "
            "implicitly in Lean); (ii) genuine extra arguments in the Lean "
            "mirror (`ValuationLemmas.deltaNonnegative`, `offWallZero`, "
            "`vp-add-min-unequal` each take an additional `fuel` argument, "
            "because the mirrored `deltaAt` is fuel-indexed); and (iii) mirrors "
            "that deliberately strengthen an assumed Agda record into a "
            "constructed Lean object (`QuotientSetoidSurface`, "
            "`UniversalOperatorBasis`), which their own headers state.\n"
            "* Conversely, agreement on this shape is weak evidence.  It rules "
            "out gross mis-transcription of arity and conclusion form; it does "
            "not rule out a mirror that states a different proposition of the "
            "same shape."
        )
    else:
        for path, m, mm, details in rows:
            print(f"{path}: {m} agree, {mm} disagree")
            for aname, lname, a, l in details:
                print(f"    {aname} -> {lname}: agda{a[0], a[2]} lean{l[0], l[2]}")
        print(f"\ntotal {total}, agree {agree}")
        print(f"postulate pairs: {len(postulate_pairs)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
