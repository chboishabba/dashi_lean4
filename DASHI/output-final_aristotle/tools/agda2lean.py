#!/usr/bin/env python3
"""Transliterate the Agda fragment used by the upstream DASHI development into
Lean 4 source that uses the Agda front end of `RequestProject.Agda.Syntax`.

Usage
-----

    python3 tools/agda2lean.py --report            # coverage over the ingested corpus
    python3 tools/agda2lean.py --emit              # write the transliterated modules
    python3 tools/agda2lean.py FILE.agda           # transliterate one file to stdout

The transliteration is purely syntactic.  It never invents mathematics: every
declaration it emits is the upstream declaration, rendered in the Lean front
end, and Lean's kernel then checks it.  Anything the front end cannot express
is reported rather than guessed at, so the report is an honest measurement of
how much of the upstream corpus the front end covers.

What is handled
---------------

* the module header, comments (`{- -}` becomes `/- -/`), and layout;
* `data`/`record` declarations, `field` blocks, `open ... public`;
* signature-plus-clauses definitions, including absurd clauses;
* `import M as A` aliases (expanded textually) and `open import M using (…)`;
* identifiers Lean cannot spell (`foo-bar`), which are quoted as `«foo-bar»`;
* binary mixfix operators `_⊕_`: the definition is hoisted into its own block,
  its clauses are rewritten to prefix form, and a Lean `infix` notation is
  emitted so that later declarations can keep using the operator.

What is reported as out of scope
--------------------------------

`where` blocks attached to a clause, `with`-abstraction, copatterns, `mutual`,
`postulate`, instance arguments, non-binary mixfix, and dependencies on Agda
modules outside the ingested corpus.
"""

from __future__ import annotations

import argparse
import os
import re
import sys
from dataclasses import dataclass, field

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CORPUS = os.path.join(ROOT, "upstream", "dashi_agda")
OUTDIR = os.path.join(ROOT, "AgdaVendor")
BLOCKED = os.path.join(ROOT, "tools", "agda2lean_blocked.txt")
SHIMS = os.path.join(ROOT, "tools", "agda2lean_shims.txt")

PRELUDE_PREFIXES = ("Agda.", "Data.", "Relation.", "Function", "Level", "Codata.")

# Identifier characters Lean accepts unquoted (a conservative subset).
LEAN_IDENT_RE = re.compile(r"^[^\s(){}\[\].,;:\"`\\]+$")
# Characters that make a name unspellable in Lean, either because Lean's own
# lexer will not take them or because the Agda prelude of
# `RequestProject.Agda.Prelude` has claimed them as notation tokens (so that
# `⊥ᶠ` would lex as `⊥` followed by `ᶠ`).
BAD_IDENT_CHARS = re.compile(r"[-?/\\+*&|^<>=~!@#$%⊥⊤≡∷∈≢×⊎∘≤≥∨∧¬⊔⊓→∅ℕℤℚ△⊕⊗]")

MIXFIX_RE = re.compile(r"^_(\S+)_$")


@dataclass
class Outcome:
    path: str
    module: str = ""
    ok: bool = False
    reasons: list[str] = field(default_factory=list)
    deps: list[str] = field(default_factory=list)
    lean: str = ""


def strip_block_comments(text: str) -> str:
    return text.replace("{-", "/-").replace("-}", "-/")


ASCII_ARROW_RE = re.compile(r"(?<![-<>=~|])->(?!>)")


def normalize_arrows(text: str) -> str:
    """Agda accepts `->` for `→`; the rest of the translator only looks for
    `→`, so the two spellings are normalised here."""
    return ASCII_ARROW_RE.sub("→", text)


OPENERS = "([{"
CLOSERS = ")]}"


def rewrite_binder_arrows(text: str) -> str:
    """Agda separates binders from bodies with `→`; Lean uses `,` (for `∀`) and
    `=>` (for `λ`).  Rewrite the first bracket-depth-zero arrow after each
    binder head."""
    out = list(text)
    i = 0
    while i < len(out):
        ch = out[i]
        if ch in ("∀", "λ", "Π"):
            depth = 0
            j = i + 1
            while j < len(out):
                c = out[j]
                if c in OPENERS:
                    depth += 1
                elif c in CLOSERS:
                    if depth == 0:
                        break
                    depth -= 1
                elif c == "→" and depth == 0:
                    if ch == "λ":
                        out[j] = "=>"
                    else:
                        out[j] = ","
                    break
                elif c in ("∀", "λ") and depth == 0:
                    break
                j += 1
        i += 1
    return "".join(out)


ABSURD_LAMBDA_RE = re.compile(r"λ((?:\s+[A-Za-z_][^\s()λ]*)*)\s*\(\s*\)")


def rewrite_absurd_lambdas(text: str) -> str:
    """Agda's absurd lambda `λ ()` refutes its argument; Lean spells that
    `nofun`.  `λ x ()` refutes the *second* argument, which is `fun x => nofun`.

    This runs before `rewrite_binder_arrows`, whose scan for the arrow that ends
    a binder would otherwise run past the `()` and rewrite an unrelated arrow.
    """
    def sub(m: re.Match) -> str:
        args = m.group(1).split()
        return "nofun" if not args else "fun " + " ".join(args) + " => nofun"
    return ABSURD_LAMBDA_RE.sub(sub, text)


def is_comment(line: str) -> bool:
    s = line.strip()
    return s.startswith("--") or s.startswith("/-") or s.startswith("-/") or s == ""


def indent_of(line: str) -> int:
    return len(line) - len(line.lstrip())


def split_top_level(text: str, sep: str) -> list[str]:
    """Split on `sep` at bracket depth zero."""
    parts, depth, cur = [], 0, []
    i = 0
    while i < len(text):
        c = text[i]
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        if depth == 0 and text.startswith(sep, i):
            parts.append("".join(cur))
            cur = []
            i += len(sep)
            continue
        cur.append(c)
        i += 1
    parts.append("".join(cur))
    return [p.strip() for p in parts]


def block_after(body: list[str], i: int, outer: int) -> tuple[list[str], int]:
    """The layout block that follows line `i`, i.e. the run of lines indented
    further than `outer`, allowing interior blank lines.  Returns the block and
    the index of the first line after it."""
    j = i + 1
    block: list[str] = []
    while j < len(body):
        if body[j].strip() == "":
            k = j
            while k < len(body) and body[k].strip() == "":
                k += 1
            if k < len(body) and indent_of(body[k]) > outer:
                block.extend(body[j:k])
                j = k
                continue
            break
        if indent_of(body[j]) <= outer:
            break
        block.append(body[j])
        j += 1
    return block, j


def unwrap_scope_blocks(body: list[str]) -> list[str]:
    """Agda's `private` and `abstract` blocks change *scope*, not content.

    A transliterated module is one Lean namespace, and the front end has no
    notion of a private name, so the block is unwrapped: its declarations are
    dedented to the enclosing level and emitted as ordinary ones.  That is
    faithful for what the corpus uses these blocks for -- local abbreviations
    that the module's public results are stated in terms of -- and it is what
    lets those results be checked at all.
    """
    out: list[str] = []
    i = 0
    while i < len(body):
        line = body[i]
        if line.strip() not in ("private", "abstract"):
            out.append(line)
            i += 1
            continue
        outer = indent_of(line)
        block, j = block_after(body, i, outer)
        inner = next((indent_of(b) for b in block if b.strip()), None)
        if inner is None:
            out.append(line)
            i += 1
            continue
        delta = inner - outer
        for b in block:
            out.append(b[delta:] if b.startswith(" " * delta) else b.lstrip())
        i = j
    return out


WITH_HEAD_RE = re.compile(r"^(?P<lhs>\S.*?)\s+with\s+(?P<scrut>\S.*?)\s*$")
DOTS_RE = re.compile(r"^\.\.\.\s*\|(?P<rest>.*)$")
REWRITE_HEAD_RE = re.compile(r"^(?P<lhs>\S.*?)\s+rewrite\s+(?P<eqs>\S.*?)\s*$")


def split_clause(text: str) -> tuple[str, str] | None:
    """Split a clause at its defining `=`, which is the first bracket-depth-zero
    `=` that is not part of an operator token (`==`, `≡`, `≤`, …)."""
    depth = 0
    for i, c in enumerate(text):
        if c in OPENERS:
            depth += 1
        elif c in CLOSERS:
            depth -= 1
        elif c == "=" and depth == 0:
            if text[i - 1: i] in ("=", "<", ">", "!", "/", ":", "≡") or text[i + 1: i + 2] == "=":
                continue
            return text[:i].rstrip(), text[i + 1:].strip()
    return None


def expand_with_clauses(body: list[str]) -> tuple[list[str], list[str]]:
    """Agda's `with`-abstraction, rendered as Lean's `match`.

    A clause

        f p₁ … pₙ with e₁ | e₂
        … | q₁ | q₂ = r₁
        … | q₁' | q₂' = r₂

    scrutinises `e₁, e₂` and continues with the given patterns, which is
    exactly `f p₁ … pₙ = match e₁, e₂ with | q₁, q₂ => r₁ | q₁', q₂' => r₂`.
    Lean's `match` abstracts the scrutinees in the expected type just as Agda's
    `with` does, so a clause whose right-hand side is a proof by computation
    still typechecks.  Nested `with` (a `…` line that itself abstracts) is
    reported rather than guessed at.
    """
    reasons: list[str] = []
    out: list[str] = []
    i = 0
    while i < len(body):
        line = body[i]
        if indent_of(line) != 0 or is_comment(line) or '"' in line:
            out.append(line)
            i += 1
            continue
        m = WITH_HEAD_RE.match(line.rstrip())
        if not m:
            out.append(line)
            i += 1
            continue
        # the alternatives: `… | …` lines with their continuations
        alts: list[list[str]] = []
        j = i + 1
        while j < len(body):
            s = body[j].strip()
            if s == "":
                k = j
                while k < len(body) and body[k].strip() == "":
                    k += 1
                if k < len(body) and body[k].strip().startswith("..."):
                    j = k
                    continue
                break
            if s.startswith("..."):
                alts.append([body[j]])
                j += 1
                continue
            if alts and indent_of(body[j]) > 0:
                alts[-1].append(body[j])
                j += 1
                continue
            break
        scruts = split_top_level(m.group("scrut"), "|")
        parsed: list[tuple[list[str], list[str]]] = []
        ok = bool(alts)
        for alt in alts:
            head = DOTS_RE.match(alt[0].strip())
            if head is None or re.search(r"\bwith\b|\brewrite\b", alt[0]):
                ok = False
                break
            piece = split_clause(head.group("rest"))
            if piece is None:
                ok = False
                break
            pats = split_top_level(piece[0], "|")
            if len(pats) != len(scruts):
                ok = False
                break
            rhs = [piece[1]] + [l.strip() for l in alt[1:]]
            parsed.append((pats, rhs))
        if not ok:
            reasons.append("with-abstraction")
            out.append(line)
            i += 1
            continue
        out.append(f"{m.group('lhs')} = match {', '.join(scruts)} with")
        for pats, rhs in parsed:
            out.append(f"  | {', '.join(pats)} => {rhs[0]}")
            for extra in rhs[1:]:
                out.append("      " + extra)
        i = j
    return out, reasons


def expand_rewrite_clauses(body: list[str]) -> tuple[list[str], list[str]]:
    """Agda's `f p₁ … pₙ rewrite e₁ | e₂ = r` rewrites the goal left to right
    by each equation and then gives `r`; that is Lean's
    `by rw [e₁, e₂] <;> exact r`.  `<;>` rather than `;` because Lean's `rw`
    closes a goal that has become reflexive, in which case there is nothing
    left for `exact` to do."""
    reasons: list[str] = []
    out: list[str] = []
    i = 0
    while i < len(body):
        line = body[i]
        if indent_of(line) != 0 or is_comment(line) or '"' in line:
            out.append(line)
            i += 1
            continue
        piece = split_clause(line.rstrip())
        m = REWRITE_HEAD_RE.match(piece[0]) if piece else None
        if piece is None or m is None:
            if re.search(r"\brewrite\b", line):
                reasons.append("rewrite clause")
            out.append(line)
            i += 1
            continue
        block, j = block_after(body, i, 0)
        if any(re.search(r"\bwith\b|\brewrite\b", b) for b in block):
            reasons.append("rewrite clause")
            out.append(line)
            i += 1
            continue
        eqs = split_top_level(m.group("eqs"), "|")
        rhs = [piece[1]] + [b.strip() for b in block if b.strip()]
        out.append(f"{m.group('lhs')} = by rw [{', '.join(eqs)}] <;> exact (")
        for r in rhs:
            out.append("    " + r)
        out.append("    )")
        i = j
    return out, reasons


SIMPLE_PATTERN_RE = re.compile(r"^(?:_|[A-Za-z«][^\s()]*)$")


def where_block_lets(block: list[str]) -> list[str] | None:
    """Render an Agda `where` block as a chain of Lean `let`s.

    Lean's own `where` cannot see the clause's pattern variables, but a `let`
    at the head of the right-hand side can, and that is what the Agda block
    means.  Each entry of the block is a signature `n : T` or a clause
    `n p₁ … pₖ = e`; entries may span several lines.  A helper with variable
    patterns becomes `let n : T := fun p₁ … pₖ => e`, and one defined by
    several clauses becomes a `fun … => match … with` -- the same shape the
    front end gives a top-level definition.  Returns `None` for a block it
    cannot read.
    """
    base = None
    entries: list[list[str]] = []
    for l in block:
        if is_comment(l):
            continue
        ind = indent_of(l)
        if base is None:
            base = ind
        if ind <= base:
            entries.append([l.strip()])
        elif entries:
            entries[-1].append(l.strip())
        else:
            return None
    if not entries:
        return None
    types: dict[str, str] = {}
    clauses: dict[str, list[tuple[list[str], str]]] = {}
    order: list[str] = []
    for e in entries:
        text = " ".join(e)
        piece = split_clause(text)
        if piece is None:
            m = re.match(r"^([^\s:]+)\s*:\s*(.+)$", text)
            if not m:
                return None
            types[m.group(1)] = m.group(2)
            continue
        lhs, rhs = piece
        toks = lhs.split()
        if not toks or not rhs:
            return None
        name, pats = toks[0], toks[1:]
        if name not in clauses:
            clauses[name] = []
            order.append(name)
        clauses[name].append((pats, rhs))
    if not order:
        return None
    lets: list[str] = []
    for name in order:
        cls = clauses[name]
        ann = f" : {types[name]}" if name in types else ""
        pats, rhs = cls[0]
        if len(cls) == 1 and all(SIMPLE_PATTERN_RE.match(p) for p in pats):
            binder = ("fun " + " ".join(pats) + " => ") if pats else ""
            lets.append(f"let {name}{ann} := {binder}{rhs}")
            continue
        arity = len(pats)
        if arity == 0 or any(len(p) != arity for p, _ in cls) or not ann:
            return None
        xs = [f"whereArg{i}" for i in range(arity)]
        lets.append(f"let {name}{ann} := fun {' '.join(xs)} => "
                    f"match {', '.join(xs)} with")
        for ps, r in cls:
            lets.append(f"  | {', '.join(ps)} => {r}")
    return lets


def hoist_where_blocks(body: list[str]) -> tuple[list[str], list[str]]:
    """Agda attaches auxiliary definitions to a clause with a `where` block.

    Lean's `where` cannot see the clause's pattern variables, so the block is
    rendered instead as a `let`-chain at the head of the right-hand side, which
    is what the Agda block means.  A block this cannot read, or one attached to
    a clause we cannot locate, is reported as out of scope."""
    reasons: list[str] = []
    out: list[str] = []
    i = 0
    while i < len(body):
        line = body[i]
        if line.strip() != "where" or indent_of(line) == 0:
            out.append(line)
            i += 1
            continue
        wi = indent_of(line)
        j = i + 1
        block: list[str] = []
        while j < len(body):
            nxt = body[j]
            if nxt.strip() == "":
                # a blank line ends the block unless more block lines follow
                k = j
                while k < len(body) and body[k].strip() == "":
                    k += 1
                if k < len(body) and indent_of(body[k]) >= wi:
                    block.extend(body[j:k])
                    j = k
                    continue
                break
            if indent_of(nxt) < wi:
                break
            block.append(nxt)
            j += 1
        lets = where_block_lets(block)
        if not lets:
            reasons.append("clause-level where block")
            out.append(line)
            i = j
            continue
        # locate the clause: the last emitted line at indent 0 containing `=`
        start = None
        for k in range(len(out) - 1, -1, -1):
            if indent_of(out[k]) == 0 and out[k].strip() and not out[k].strip().startswith("--"):
                start = k
                break
        if start is None or "=" not in out[start]:
            reasons.append("clause-level where block")
            out.append(line)
            i = j
            continue
        head, rhs = out[start].split("=", 1)
        rest = out[start + 1:]
        out = out[:start]
        out.append(head.rstrip() + " =")
        for l in lets:
            out.append("  " + l)
        if rhs.strip():
            out.append("  " + rhs.strip())
        for l in rest:
            out.append(("  " + l) if l.strip() else l)
        i = j
    return out, reasons


def needs_quoting(name: str) -> bool:
    if MIXFIX_RE.match(name):
        return True
    return bool(BAD_IDENT_CHARS.search(name))


def quote_name(name: str) -> str:
    return f"«{name}»"


def collect_names(lines: list[str]) -> tuple[set[str], dict[str, str]]:
    """Names declared at the top level of the module, and mixfix operators."""
    names: set[str] = set()
    mixfix: dict[str, str] = {}
    for line in lines:
        if is_comment(line):
            continue
        stripped = line.rstrip()
        head = stripped.lstrip()
        indent = len(stripped) - len(head)
        toks = head.split()
        if not toks:
            continue
        if indent == 0:
            if toks[0] in ("data", "record") and len(toks) > 1:
                names.add(toks[1])
            elif ":" in toks and toks[0] not in ("open", "import", "module",
                                                 "infix", "infixl", "infixr"):
                # a signature: `name : type`, or `a b c : type` inside a block
                idx = toks.index(":")
                for t in toks[:idx]:
                    names.add(t)
                    m = MIXFIX_RE.match(t)
                    if m:
                        mixfix[t] = m.group(1)
        else:
            # constructor / field lines
            if ":" in toks:
                idx = toks.index(":")
                for t in toks[:idx]:
                    if t not in ("constructor", "field"):
                        names.add(t)
            elif len(toks) == 2 and toks[0] == "constructor":
                names.add(toks[1])
    return names, mixfix


def rename_tokens(line: str, renames: dict[str, str]) -> str:
    if not renames:
        return line
    out = []
    for tok in re.split(r"(\s+|\(|\)|\{|\})", line):
        out.append(renames.get(tok, tok))
    return "".join(out)


def transliterate(path: str, corpus_modules: set[str]) -> Outcome:
    out = Outcome(path=path)
    raw = open(path, encoding="utf-8").read()
    text = rewrite_binder_arrows(
        rewrite_absurd_lambdas(normalize_arrows(strip_block_comments(raw))))
    lines = text.split("\n")

    header = None
    for i, line in enumerate(lines):
        if line.startswith("module "):
            m = re.match(r"module\s+(\S+)\s+where\s*$", line)
            if not m:
                out.reasons.append("parametrised or malformed module header")
                return out
            header = m.group(1)
            body = lines[i + 1:]
            break
    else:
        out.reasons.append("no module header")
        return out
    out.module = header

    body = unwrap_scope_blocks(body)
    body, where_reasons = hoist_where_blocks(body)
    out.reasons.extend(where_reasons)
    body, with_reasons = expand_with_clauses(body)
    out.reasons.extend(with_reasons)
    body, rewrite_reasons = expand_rewrite_clauses(body)
    out.reasons.extend(rewrite_reasons)

    # unsupported constructs
    for line in body:
        s = line.strip()
        if re.match(r"^postulate\b", s):
            out.reasons.append("postulate")
        if re.match(r"^mutual\b", s):
            out.reasons.append("mutual block")
        if s in ("private", "abstract"):
            out.reasons.append("private/abstract block")
        if re.match(r"^variable\b", s):
            out.reasons.append("variable block")
        if (s.endswith(" with") and not re.search(r"\bmatch\b", s)) or s.startswith("..."):
            out.reasons.append("with-abstraction")
        if s == "where":
            out.reasons.append("clause-level where block")
        if "λ where" in s:
            out.reasons.append("lambda without arrow")
        if "Σ[" in s or "∃" in s:
            out.reasons.append("sigma/exists syntax")
        if "{{" in s:
            out.reasons.append("instance arguments")
    # A lambda whose arrow the binder rewriting did not reach -- a pattern
    # lambda, say -- would elaborate as something else entirely.
    joined = "\n".join(body)
    for m in re.finditer("λ", joined):
        rest = joined[m.end():]
        nxt = rest.find("λ")
        if "=>" not in (rest if nxt < 0 else rest[:nxt]):
            out.reasons.append("lambda without arrow")
            break

    # dependencies and alias expansion
    deps: list[str] = []
    aliases: dict[str, str] = {}
    kept: list[str] = []
    for line in body:
        s = line.strip()
        m = re.match(r"^import\s+(\S+)\s+as\s+(\S+)\s*$", s)
        if m:
            aliases[m.group(2)] = m.group(1)
            deps.append(m.group(1))
            kept.append(f"open import {m.group(1)}")
            continue
        m = re.match(r"^open\s+import\s+(\S+)", s)
        if m:
            deps.append(m.group(1))
            # Agda's `using (…)` list only restricts scope; it may also mention
            # mixfix names that Lean cannot spell, so it is dropped.
            kept.append(f"open import {m.group(1)}")
            continue
        m = re.match(r"^import\s+(\S+)\s*$", s)
        if m:
            # A bare `import M` makes `M`'s qualified names available; the
            # transliterated module is one namespace per Agda module, so opening
            # the namespace is the same thing.
            deps.append(m.group(1))
            kept.append(f"open import {m.group(1)}")
            continue
        kept.append(line)
    body = kept

    for d in deps:
        if d.startswith(PRELUDE_PREFIXES):
            continue
        if d not in corpus_modules:
            out.reasons.append(f"dependency outside the ingested corpus: {d}")
    out.deps = sorted({d for d in deps if not d.startswith(PRELUDE_PREFIXES)})

    names, mixfix = collect_names(body)
    renames = {n: quote_name(n) for n in names if needs_quoting(n)}
    for alias, target in aliases.items():
        renames[alias] = target

    for op in mixfix:
        if not re.match(r"^_\S+_$", op):
            out.reasons.append(f"unsupported mixfix shape: {op}")

    # alias-qualified names (`Four.polarPosition`) need the alias expanded too
    def expand_aliases(line: str) -> str:
        for alias, target in aliases.items():
            line = re.sub(rf"(?<![\w.]){re.escape(alias)}\.", target + ".", line)
        return line

    fixities: dict[str, tuple[str, int]] = {}
    processed: list[str] = []
    for line in body:
        s = line.strip()
        m = re.match(r"^(infix|infixl|infixr)\s+(\d+)\s+(\S.*)$", s)
        if m:
            # Agda's fixity declaration: the operators it mentions get a Lean
            # `notation` of their own where the front end supports them, and the
            # declaration itself is dropped (Lean has no such command inside a
            # layout block).
            for op in m.group(3).split():
                fixities[op] = (m.group(1), 10 * int(m.group(2)))
            continue
        processed.append(expand_aliases(line))
    body = processed

    if out.reasons:
        return out

    # One Lean command per Agda declaration.  Lean parses a command before it
    # elaborates the next one, so a notation emitted for a mixfix operator in
    # one declaration is available to every later declaration — which is what
    # makes mixfix operators usable at all.
    segments: list[tuple[str, object]] = []  # ("block", lines) | ("notation", …)
    pendingcomments: list[str] = []
    i = 0
    while i < len(body):
        line = body[i]
        if line.strip() == "" or is_comment(line):
            pendingcomments.append(line)
            i += 1
            continue
        if indent_of(line) != 0:
            # stray continuation; keep it with the previous block
            if segments and segments[-1][0] == "block":
                segments[-1][1].extend(pendingcomments + [line])
                pendingcomments = []
            i += 1
            continue
        toks = line.strip().split()
        decl = pendingcomments + [line]
        pendingcomments = []
        head = toks[0]
        is_sig = len(toks) >= 2 and toks[1] == ":"
        opsym = mixfix.get(head) if is_sig else None

        def continues(l: str) -> bool:
            """Is this indent-0 line another clause of the declaration?"""
            if not is_sig:
                return False
            if l.strip().split()[:1] == [head]:
                return True
            return opsym is not None and f" {opsym} " in l and "=" in l
        i += 1
        # continuation lines, then (for a signature) the clauses of the same name
        while i < len(body):
            nxt = body[i]
            if nxt.strip() == "":
                # a blank line only ends the declaration if what follows starts one
                j = i
                while j < len(body) and body[j].strip() == "":
                    j += 1
                if j < len(body) and indent_of(body[j]) == 0 and not continues(body[j]):
                    break
                if j >= len(body):
                    break
                decl.extend(body[i:j])
                i = j
                continue
            if indent_of(nxt) > 0:
                decl.append(nxt)
                i += 1
                continue
            if continues(nxt):
                decl.append(nxt)
                i += 1
                continue
            break
        if (not is_sig) and len(toks) >= 2 and toks[0] in ("data", "record") \
                and MIXFIX_RE.match(toks[1]):
            opname = toks[1]
            sym = MIXFIX_RE.match(opname).group(1)
            pat = re.compile(rf"(\S+)\s+{re.escape(sym)}\s+(\([^()]*\)|\S+)")
            rewritten = []
            for l in decl:
                if is_comment(l):
                    rewritten.append(l)
                    continue
                l = l.replace(f"{toks[0]} {opname}", f"{toks[0]} {quote_name(opname)}")
                l = pat.sub(lambda m: f"{quote_name(opname)} {m.group(1)} {m.group(2)}", l)
                rewritten.append(l)
            segments.append(("block", rewritten))
            segments.append(("notation", (opname, sym, fixities.get(opname, ("infix", 500)))))
        elif is_sig and head in mixfix:
            sym = mixfix[head]
            rewritten = []
            for l in decl:
                s2 = l.strip()
                if is_comment(l) or indent_of(l) > 0:
                    rewritten.append(l)
                    continue
                if s2.split()[:2] == [head, ":"]:
                    rewritten.append(f"{quote_name(head)} :" + s2.split(":", 1)[1])
                elif f" {sym} " in s2 and "=" in s2 \
                        and f" {sym} " in s2.split("=", 1)[0]:
                    lhs, rhs = s2.split("=", 1)
                    left, right = lhs.split(f" {sym} ", 1)
                    rewritten.append(
                        f"{quote_name(head)} {left.strip()} {right.strip()} ={rhs}")
                else:
                    rewritten.append(l)
            segments.append(("block", rewritten))
            segments.append(("notation", (head, sym, fixities.get(head, ("infixl", 500)))))
        else:
            segments.append(("block", decl))
    if pendingcomments:
        segments.append(("block", pendingcomments))

    # emit
    lean: list[str] = []
    lean.append("import RequestProject.Agda.Syntax")
    for d in out.deps:
        lean.append(f"import AgdaVendor.{d}")
    lean.append("")
    lean.append("/-!")
    lean.append(f"# `{header}`, transliterated")
    lean.append("")
    lean.append("Generated by `tools/agda2lean.py` from the ingested upstream source")
    lean.append(f"`upstream/dashi_agda/{os.path.relpath(path, CORPUS)}`.")
    lean.append("Do not edit by hand: re-run the translator instead.")
    lean.append("-/")
    lean.append("")
    lean.append("open Agda")
    lean.append("")
    # Each declaration becomes its own `agda_module` block, and a Lean `open`
    # inside one does not survive the end of its namespace block.  An Agda
    # `open import` is in scope for the whole module, so it is re-issued at the
    # head of every later block.
    opens: list[str] = []
    for kind, payload in segments:
        if kind == "block":
            block = [rename_tokens(l, renames) for l in payload]
            if all(is_comment(l) for l in block):
                continue
            lean.append(f"agda_module {header} where")
            for l in opens:
                lean.append("  " + l)
            for l in block:
                lean.append(("  " + l).rstrip())
            lean.append("")
            for l in block:
                s = l.strip()
                if s.startswith("open import ") and s not in opens:
                    opens.append(s)
        else:
            opname, sym, (fix, prec) = payload
            lean.append(f'{fix}:{prec} " {sym} " => {header}.{quote_name(opname)}')
            lean.append("")
    out.lean = "\n".join(lean) + "\n"
    out.ok = True
    return out


def corpus_files() -> list[str]:
    files = []
    for base, _dirs, names in os.walk(CORPUS):
        for n in names:
            if n.endswith(".agda"):
                files.append(os.path.join(base, n))
    return sorted(files)


def module_of(path: str) -> str:
    for line in open(path, encoding="utf-8"):
        m = re.match(r"module\s+(\S+)\s+where", line)
        if m:
            return m.group(1)
    return ""


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("file", nargs="?")
    ap.add_argument("--report", action="store_true")
    ap.add_argument("--emit", action="store_true")
    args = ap.parse_args()

    files = corpus_files()
    modules = {module_of(f) for f in files}

    if args.file:
        out = transliterate(args.file, modules)
        if out.ok:
            sys.stdout.write(out.lean)
        else:
            print(f"not transliterated: {'; '.join(sorted(set(out.reasons)))}", file=sys.stderr)
            return 1
        return 0

    # Prefer the branch copies of a module over the master copy: the branches
    # are where the new upstream work is.
    priority = ["agent/evidence-polarity-cross-pollination",
                "agent/progenitor-parent-hyperfabric", "master"]

    def rank(path: str) -> int:
        rel = os.path.relpath(path, CORPUS)
        for i, b in enumerate(priority):
            if rel.startswith(b + os.sep):
                return i
        return len(priority)

    files = sorted(files, key=lambda f: (module_of(f), rank(f)))
    seen: set[str] = set()
    unique = []
    for f in files:
        m = module_of(f)
        if m in seen:
            continue
        seen.add(m)
        unique.append(f)
    files = unique

    shims: set[str] = set()
    if os.path.exists(SHIMS):
        for line in open(SHIMS, encoding="utf-8"):
            line = line.split("#")[0].strip()
            if line:
                shims.add(line)

    blocked: set[str] = set()
    if os.path.exists(BLOCKED):
        for line in open(BLOCKED, encoding="utf-8"):
            line = line.split("#")[0].strip()
            if line:
                blocked.add(line)

    results = [transliterate(f, modules) for f in files]
    for r in results:
        if r.module in shims:
            # a hand-written Lean module stands in for this one
            r.ok = True
            r.reasons = ["hand-written Lean shim"]
            r.lean = ""
            r.deps = []
            continue
        if r.module in blocked:
            r.ok = False
            r.reasons.append("front end cannot elaborate this module yet")
    # A module can only be emitted if everything it depends on can be too.
    by_module = {r.module: r for r in results}
    changed = True
    while changed:
        changed = False
        for r in results:
            if not r.ok:
                continue
            for d in r.deps:
                dep = by_module.get(d)
                if dep is None or not dep.ok:
                    r.ok = False
                    r.reasons.append(f"dependency not transliterable: {d}")
                    changed = True
                    break
    ok = [r for r in results if r.ok]
    if args.report:
        print(f"corpus: {len(results)} Agda modules under upstream/dashi_agda")
        print(f"transliterated: {len(ok)}")
        reasons: dict[str, int] = {}
        for r in results:
            if r.ok:
                continue
            for reason in sorted(set(r.reasons)):
                key = reason.split(":")[0]
                reasons[key] = reasons.get(key, 0) + 1
        print("blocked by:")
        for k, v in sorted(reasons.items(), key=lambda kv: -kv[1]):
            print(f"  {v:4d}  {k}")
        print()
        for r in results:
            status = "ok  " if r.ok else "skip"
            print(f"{status}  {r.module or os.path.relpath(r.path, CORPUS)}"
                  + ("" if r.ok else "   [" + "; ".join(sorted(set(r.reasons))) + "]"))
    if args.emit:
        shim_paths = {os.path.join(OUTDIR, *m.split(".")) + ".lean" for m in shims}
        for base, _dirs, names in os.walk(OUTDIR):
            for n in names:
                path = os.path.join(base, n)
                if n.endswith(".lean") and path not in shim_paths:
                    os.remove(path)
        written = 0
        for r in ok:
            if not r.lean:
                continue
            dest = os.path.join(OUTDIR, *r.module.split(".")) + ".lean"
            os.makedirs(os.path.dirname(dest), exist_ok=True)
            with open(dest, "w", encoding="utf-8") as fh:
                fh.write(r.lean)
            written += 1
        print(f"wrote {written} Lean modules under {os.path.relpath(OUTDIR, ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
