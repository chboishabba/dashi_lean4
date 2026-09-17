#!/usr/bin/env python3
"""Provenance and dependency analysis for the Lean 4 Wikidata port.

Answers, from the sources themselves:

  * which declarations come from the DASHI Agda bridge, which come from the
    Wikidata data model / standards, and which are original to this port;
  * what depends on what (the real, kernel-level dependency graph);
  * how many items *need* each source, and how much of each item's support
    comes from where.

Outputs (all under ``docs/status/``):

  * ``provenance.json``     -- machine-readable attribution + dependency data
  * ``PROVENANCE.md``       -- the written report
  * ``dependencies.dot``    -- module dependency graph in Graphviz form
  * ``dependencies.svg``    -- the same graph, rendered without Graphviz
  * ``dashi.svg``           -- the DASHI-focused infographic

and, outside ``docs/``:

  * ``RequestProject/Meta/Provenance.lean`` -- the machine-checked ledger
  * ``-- @source ...`` attribution lines in the Lean sources (``--annotate``)

Usage from the repository root::

    lake env lean tools/DepDump.lean      # refresh docs/status/deps.json
    python3 tools/provenance.py           # analyse + write the artefacts
    python3 tools/provenance.py --annotate  # also rewrite the @source lines
"""

from __future__ import annotations

import json
import math
import os
import re
import sys
from collections import Counter, OrderedDict, defaultdict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "RequestProject")
OUT_DIR = os.path.join(ROOT, "docs", "status")

# ---------------------------------------------------------------------------
# Sources
# ---------------------------------------------------------------------------

SOURCES = OrderedDict(
    [
        ("dashi", {"label": "DASHI Agda bridge (PR #555 / #581 / #582)", "colour": "#f0883e"}),
        ("wikidata", {"label": "Wikidata data model & standards", "colour": "#1f6feb"}),
        ("original", {"label": "Original to this Lean port", "colour": "#3fb950"}),
    ]
)

# Modules whose *subject matter* is the Wikidata data model: a declaration in
# one of these that is not traced to the DASHI bridge is attributed to Wikidata
# when it mentions the vocabulary (see WIKIDATA_TOKENS), otherwise to this port.
WIKIDATA_MODULES = {
    "Wikidata/Core.lean",
    "Wikidata/ClassAlgebra.lean",
    "Wikidata/Redundancy.lean",
    "Wikidata/Diagnostics.lean",
    "Wikidata/Alignment.lean",
    "Wikidata/Provenance.lean",
    "Wikidata/Slices.lean",
    "Wikidata/Layers.lean",
    "Wikidata/Rdf.lean",
    "Wikidata/BlankNodes.lean",
    "Wikidata/Constraints.lean",
    "Wikidata/Identity.lean",
    "Wikidata/Values.lean",
    "Wikidata/Qualifiers.lean",
    "Wikidata/Sparql.lean",
    "Wikidata/Owl.lean",
    "Wikidata/Lens.lean",
    "Wikidata/DerivationFibres.lean",
    "Wikidata/Attribution.lean",
    "Wikidata/AlignmentSafety.lean",
    "Wikidata/DisjointUnionDiagnostics.lean",
    "Wikidata/RdfInformationOrder.lean",
    "Wikidata/Parenting.lean",
    "Wikidata/ParentingRoles.lean",
    "Wikidata/ParentingFibres.lean",
    "Wikidata/ParentingAuthority.lean",
    "Wikidata/Examples.lean",
    "Wikidata/ExamplesLayers.lean",
    "Wikidata/ExamplesConflict.lean",
    "Wikidata/EvidencePolarity.lean",
    "Wikidata/Learning.lean",
    "Wikidata/ViewJoin.lean",
    "Wikidata/SparqlPaths.lean",
    "Wikidata/SparqlAggregation.lean",
    "Wikidata/SparqlNegation.lean",
    "Wikidata/ClassExpressions.lean",
    "Wikidata/NamedGraphs.lean",
    "Wikidata/Reachability.lean",
    "Wikidata/Coverage.lean",
    "Wikidata/BFO.lean",
    "Wikidata/ClassOrder.lean",
}

# Vocabulary that only makes sense because Wikidata (or the RDF stack it is
# published in) defines it.  Matched against the declaration's source text.
WIKIDATA_TOKENS = [
    r"\bP\d{1,5}\b",
    r"\bQ\d{1,7}\b",
    r"\bQid\b",
    r"\bPid\b",
    r"[Tt]ruthy",
    r"[Rr]ank\b",
    r"deprecated",
    r"preferred",
    r"subclassOf",
    r"instanceOf",
    r"sitelink",
    r"[Ll]exeme",
    r"[Rr]eif",
    r"[Tt]riple",
    r"[Ss]nak",
    r"[Cc]onstraint",
    r"[Ss]chema",
    r"[Ss]itelink",
    r"externalId",
    r"ExternalId",
    r"[Kk]nowledgeBase",
    r"\bKB\b",
    r"[Ss]tatement",
    r"[Pp]rovenance",
    r"partOf",
    r"PartOf",
]
WIKIDATA_RE = re.compile("|".join(WIKIDATA_TOKENS))

# ---------------------------------------------------------------------------
# Parsing the Lean sources
# ---------------------------------------------------------------------------

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?"
    r"(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+|nonrec\s+|scoped\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|instance|class|example)\b"
    r"(?:\s+([A-Za-z_][A-Za-z_0-9'!?]*(?:\.[A-Za-z_][A-Za-z_0-9'!?]*)*))?"
)
NAMESPACE_RE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z_0-9'.]*)")
END_RE = re.compile(r"^end(?:\s+([A-Za-z_][A-Za-z_0-9'.]*))?\s*$")
SOURCE_TAG_RE = re.compile(r"^\s*--\s*@source\b")
IMPORT_RE = re.compile(r"^import\s+([A-Za-z_][A-Za-z_0-9'.]*)")


# Generated files that describe the development rather than belong to it.
EXCLUDED = {"Meta/Provenance.lean"}


def lean_files():
    out = []
    for dirpath, _dirs, files in os.walk(SRC):
        for f in sorted(files):
            if f.endswith(".lean"):
                p = os.path.join(dirpath, f)
                rel = os.path.relpath(p, SRC).replace(os.sep, "/")
                if rel not in EXCLUDED:
                    out.append(rel)
    return sorted(out)


def module_name(rel: str) -> str:
    return "RequestProject." + rel[: -len(".lean")].replace("/", ".")


class Decl:
    __slots__ = (
        "name",
        "kind",
        "file",
        "line",
        "endline",
        "text",
        "source",
        "reason",
        "upstream",
        "uses",
        "kernel_kind",
    )

    def __init__(self, name, kind, file, line):
        self.name = name
        self.kind = kind
        self.file = file
        self.line = line
        self.endline = line
        self.text = ""
        self.source = "original"
        self.reason = ""
        self.upstream = ""
        self.uses = set()
        self.kernel_kind = "thm" if kind in ("theorem", "lemma") else "def"


def parse_file(rel: str):
    """Return (imports, [Decl]) for one Lean file, with declaration bodies."""
    path = os.path.join(SRC, rel)
    with open(path, encoding="utf-8") as fh:
        lines = fh.read().split("\n")
    ns_stack = []
    decls = []
    imports = []
    in_block_comment = 0
    for i, raw in enumerate(lines):
        line = raw.rstrip()
        stripped = line.strip()
        # crude block-comment tracking (the sources only use /-! ... -/ and /- ... -/)
        opens = stripped.count("/-")
        closes = stripped.count("-/")
        if in_block_comment:
            in_block_comment += opens - closes
            if in_block_comment < 0:
                in_block_comment = 0
            continue
        if opens > closes:
            in_block_comment += opens - closes
            continue
        m = IMPORT_RE.match(line)
        if m:
            imports.append(m.group(1))
            continue
        m = NAMESPACE_RE.match(line)
        if m:
            ns_stack.append(m.group(1))
            continue
        m = END_RE.match(line)
        if m and ns_stack:
            ns_stack.pop()
            continue
        m = DECL_RE.match(line)
        if m and m.group(2):
            kind, short = m.group(1), m.group(2)
            full = ".".join(ns_stack + [short]) if ns_stack else short
            d = Decl(full, kind, rel, i + 1)
            decls.append(d)
    # attach bodies: from the declaration line to the line before the next one
    for j, d in enumerate(decls):
        stop = decls[j + 1].line - 1 if j + 1 < len(decls) else len(lines)
        d.endline = stop
        d.text = "\n".join(
            ln for ln in lines[d.line - 1 : stop] if not SOURCE_TAG_RE.match(ln)
        )
    return imports, decls


# ---------------------------------------------------------------------------
# The upstream correspondence: which declarations the porting notes trace to
# the DASHI bridge.  Parsed out of the documents themselves, so the attribution
# is auditable and cannot drift from the notes.
# ---------------------------------------------------------------------------

BACKTICK_RE = re.compile(r"`([^`]+)`")
NAME_RE = re.compile(r"^[A-Za-z_][A-Za-z_0-9'!?]*(?:\.[A-Za-z_][A-Za-z_0-9'!?]*)*$")


def _names_in(cell: str):
    out = []
    for chunk in BACKTICK_RE.findall(cell):
        for piece in re.split(r"[\s,/]+", chunk.strip()):
            piece = piece.strip("().;:")
            if NAME_RE.match(piece) and not piece.endswith(".lean"):
                out.append(piece)
    return out


def upstream_rows():
    """[(idea, [names])] from the correspondence tables of the notes."""
    rows = []
    for fname, section_filter in (
        ("PORTING_NOTES.md", None),
        ("RELATED_WORK.md", "1."),
    ):
        path = os.path.join(ROOT, fname)
        if not os.path.exists(path):
            continue
        with open(path, encoding="utf-8") as fh:
            text = fh.read()
        if section_filter is not None:
            # only section 1 of RELATED_WORK is about the DASHI bridge
            start = text.find("## 1.")
            end = text.find("## 2.")
            text = text[start : end if end > 0 else len(text)]
        for line in text.split("\n"):
            if not line.startswith("|"):
                continue
            cells = [c.strip() for c in line.strip().strip("|").split("|")]
            if len(cells) < 2:
                continue
            if set("".join(cells)) <= set("- "):
                continue
            idea, rendering = cells[0], cells[-1]
            if idea.lower().startswith("idea in") or idea.lower().startswith("#"):
                if len(cells) >= 3 and cells[1].lower().startswith("invariant"):
                    continue
                if idea.lower().startswith("idea in"):
                    continue
            if len(cells) >= 3:
                idea = cells[-2] if cells[0].strip().isdigit() else cells[0]
                if cells[0].strip().isdigit():
                    idea = "invariant %s: %s" % (cells[0].strip(), cells[1])
            names = _names_in(rendering)
            if names:
                rows.append((re.sub(r"\s+", " ", idea).strip(), names))
        if section_filter is not None:
            # §1.3 of RELATED_WORK lists, as bullets, the constructions taken
            # from the bridge in the third pass.
            for line in text.split("\n"):
                m = re.match(r"^\s*[*-]\s+`([^`]+)`\s*[—-]\s*(.+)$", line)
                if not m:
                    continue
                head, gloss = m.group(1), m.group(2)
                if ".lean" in head or "/" in head:
                    continue
                names = _names_in("`%s`" % head)
                if names:
                    rows.append((re.sub(r"\s+", " ", gloss).strip()[:160], names))
    return rows


def build_upstream_index(known_names):
    """name -> upstream idea text, resolving short names against the sources."""
    short_index = defaultdict(list)
    for n in known_names:
        short_index[n.split(".")[-1]].append(n)
    index = {}
    for idea, names in upstream_rows():
        for n in names:
            targets = []
            if n in known_names:
                targets = [n]
            elif "." in n:
                # qualified suffix match, e.g. `Certificate.holds_of_supported`
                targets = [k for k in known_names if k.endswith("." + n)]
            else:
                # bare short name: accept only when it is unambiguous
                cands = short_index.get(n, [])
                targets = cands if len(cands) == 1 else []
            for t in targets:
                index.setdefault(t, idea)
    return index


# ---------------------------------------------------------------------------
# Attribution
# ---------------------------------------------------------------------------


def classify(decls, upstream_index):
    for d in decls:
        if d.name in upstream_index:
            d.source = "dashi"
            d.upstream = upstream_index[d.name]
            d.reason = "traced to the bridge correspondence tables"
        elif d.file in WIKIDATA_MODULES and WIKIDATA_RE.search(d.text or ""):
            d.source = "wikidata"
            d.reason = "states Wikidata data-model vocabulary"
        else:
            d.source = "original"
            d.reason = "introduced by this port"


# ---------------------------------------------------------------------------
# Dependency data from the kernel dump
# ---------------------------------------------------------------------------


def load_kernel_deps(decls_by_name):
    """Attach kernel-level dependencies, resolved onto source declarations."""
    path = os.path.join(OUT_DIR, "deps.json")
    if not os.path.exists(path):
        sys.stderr.write(
            "docs/status/deps.json missing; run `lake env lean tools/DepDump.lean`\n"
        )
        return False
    with open(path, encoding="utf-8") as fh:
        records = json.load(fh)

    def resolve(name):
        """Longest prefix of `name` that is a source declaration."""
        parts = name.split(".")
        for k in range(len(parts), 0, -1):
            cand = ".".join(parts[:k])
            if cand in decls_by_name:
                return cand
        return None

    for rec in records:
        owner = resolve(rec["name"])
        if owner is None:
            continue
        d = decls_by_name[owner]
        for u in rec["uses"]:
            t = resolve(u)
            if t is not None and t != owner:
                d.uses.add(t)
    return True


def transitive_closure(decls_by_name):
    order = list(decls_by_name)
    closure = {}

    def visit(n, stack):
        if n in closure:
            return closure[n]
        if n in stack:
            return set()
        stack.add(n)
        acc = set()
        for m in decls_by_name[n].uses:
            if m in decls_by_name:
                acc.add(m)
                acc |= visit(m, stack)
        stack.discard(n)
        closure[n] = acc
        return acc

    sys.setrecursionlimit(10000)
    for n in order:
        visit(n, set())
    return closure


# ---------------------------------------------------------------------------
# Analysis
# ---------------------------------------------------------------------------


def analyse():
    files = lean_files()
    all_decls = []
    imports = {}
    file_lines = {}
    for rel in files:
        imp, ds = parse_file(rel)
        imports[rel] = imp
        with open(os.path.join(SRC, rel), encoding="utf-8") as fh:
            file_lines[rel] = len(fh.read().splitlines())
        all_decls.extend(ds)
    by_name = {d.name: d for d in all_decls}
    upstream_index = build_upstream_index(set(by_name))
    classify(all_decls, upstream_index)
    have_kernel = load_kernel_deps(by_name)
    closure = transitive_closure(by_name)

    # per-declaration support profile
    dependents = Counter()
    for d in all_decls:
        for t in closure[d.name]:
            dependents[t] += 1
    decl_records = []
    for d in all_decls:
        c = Counter(by_name[t].source for t in closure[d.name])
        decl_records.append(
            {
                "name": d.name,
                "kind": d.kernel_kind,
                "keyword": d.kind,
                "file": d.file,
                "module": module_name(d.file),
                "line": d.line,
                "source": d.source,
                "upstream": d.upstream,
                "reason": d.reason,
                "direct_uses": sorted(d.uses),
                "needs": {s: c.get(s, 0) for s in SOURCES},
                "needs_total": sum(c.values()),
                "used_by": dependents[d.name],
            }
        )
    rec_by_name = {r["name"]: r for r in decl_records}

    # module-level aggregation
    module_records = OrderedDict()
    for rel in files:
        ds = [d for d in all_decls if d.file == rel]
        c = Counter(d.source for d in ds)
        needs = Counter()
        for d in ds:
            for t in closure[d.name]:
                if by_name[t].file != rel:
                    needs[by_name[t].source] += 1
        module_records[rel] = {
            "file": rel,
            "module": module_name(rel),
            "lines": file_lines[rel],
            "declarations": len(ds),
            "theorems": sum(1 for d in ds if d.kernel_kind == "thm"),
            "definitions": sum(1 for d in ds if d.kernel_kind == "def"),
            "by_source": {s: c.get(s, 0) for s in SOURCES},
            "imports": sorted(imports[rel]),
            "external_needs": {s: needs.get(s, 0) for s in SOURCES},
            "needs_dashi_items": sum(
                1 for d in ds if rec_by_name[d.name]["needs"]["dashi"] > 0
            ),
            "needs_items": {
                src: sum(1 for d in ds if rec_by_name[d.name]["needs"][src] > 0)
                for src in SOURCES
            },
        }

    # module dependency graph, weighted by declaration-level edges
    edges = Counter()
    for d in all_decls:
        for t in d.uses:
            tf = by_name[t].file
            if tf != d.file:
                edges[(d.file, tf)] += 1
    graph_nodes = [
        rel for rel in files if module_records[rel]["declarations"] > 0
    ]
    graph_edges = [
        {"from": a, "to": b, "weight": w}
        for (a, b), w in sorted(edges.items(), key=lambda kv: -kv[1])
        if a in graph_nodes and b in graph_nodes
    ]

    # layering (longest path from a source), and a topological order
    succ = defaultdict(set)
    pred = defaultdict(set)
    for e in graph_edges:
        succ[e["from"]].add(e["to"])
        pred[e["to"]].add(e["from"])
    depth = {}

    def compute_depth(n, stack=()):
        if n in depth:
            return depth[n]
        if n in stack:
            return 0
        d = 0
        for m in succ[n]:
            d = max(d, compute_depth(m, stack + (n,)) + 1)
        depth[n] = d
        return d

    for n in graph_nodes:
        compute_depth(n)
    topo = sorted(graph_nodes, key=lambda n: (depth[n], n))

    totals = Counter(d.source for d in all_decls)
    thm_totals = Counter(d.source for d in all_decls if d.kernel_kind == "thm")
    def_totals = Counter(d.source for d in all_decls if d.kernel_kind == "def")

    reach = {
        s: sum(1 for r in decl_records if r["needs"][s] > 0) for s in SOURCES
    }
    dashi_impact = sorted(
        (r for r in decl_records if r["source"] == "dashi"),
        key=lambda r: -r["used_by"],
    )

    # how much of an item's support comes from the bridge
    bucket_defs = [("none", 0.0, 0.0), ("1–25%", 0.0, 0.25), ("26–50%", 0.25, 0.5),
                   ("51–75%", 0.5, 0.75), ("76–100%", 0.75, 1.0)]
    buckets = OrderedDict((b[0], 0) for b in bucket_defs)
    buckets["no support set"] = 0
    for r in decl_records:
        if r["needs_total"] == 0:
            buckets["no support set"] += 1
            continue
        share = r["needs"]["dashi"] / r["needs_total"]
        if share == 0.0:
            buckets["none"] += 1
            continue
        for label, lo, hi in bucket_defs[1:]:
            if lo < share <= hi:
                buckets[label] += 1
                break

    supports = sorted(len(closure[d.name]) for d in all_decls)
    median_support = supports[len(supports) // 2] if supports else 0

    return {
        "generated_by": "tools/provenance.py",
        "kernel_dependencies": have_kernel,
        "dashi_modules": sum(
            1 for m in module_records.values() if m["by_source"]["dashi"] > 0
        ),
        "median_support": median_support,
        "dashi_share_buckets": buckets,
        "max_support": supports[-1] if supports else 0,
        "longest_chain": (max(depth.values()) + 1) if depth else 0,
        "invariants": bridge_invariants(),
        "sources": {s: SOURCES[s]["label"] for s in SOURCES},
        "totals": {
            "modules": len(files),
            "modules_with_declarations": len(graph_nodes),
            "lines": sum(file_lines.values()),
            "declarations": len(all_decls),
            "theorems": sum(1 for d in all_decls if d.kernel_kind == "thm"),
            "definitions": sum(1 for d in all_decls if d.kernel_kind == "def"),
            "by_source": {s: totals.get(s, 0) for s in SOURCES},
            "theorems_by_source": {s: thm_totals.get(s, 0) for s in SOURCES},
            "definitions_by_source": {s: def_totals.get(s, 0) for s in SOURCES},
            "dependency_edges": sum(len(d.uses) for d in all_decls),
            "module_edges": len(graph_edges),
            "items_needing": reach,
        },
        "modules": list(module_records.values()),
        "declarations": decl_records,
        "graph": {
            "nodes": [
                {
                    "file": n,
                    "module": module_name(n),
                    "depth": depth[n],
                    "by_source": module_records[n]["by_source"],
                    "declarations": module_records[n]["declarations"],
                }
                for n in graph_nodes
            ],
            "edges": graph_edges,
            "topological_order": topo,
        },
        "dashi_impact": [
            {
                "name": r["name"],
                "module": r["module"],
                "used_by": r["used_by"],
                "upstream": r["upstream"],
            }
            for r in dashi_impact[:25]
        ],
    }


# ---------------------------------------------------------------------------
# Small SVG helpers
# ---------------------------------------------------------------------------


def esc(s: str) -> str:
    return (
        str(s)
        .replace("&", "&amp;")
        .replace("<", "&lt;")
        .replace(">", "&gt;")
        .replace('"', "&quot;")
    )


def text(x, y, s, size=14, fill="#c9d1d9", weight="normal", anchor="start",
         family="'DejaVu Sans', 'Segoe UI', sans-serif", opacity=1.0, extra=""):
    return (
        f'<text x="{x:.1f}" y="{y:.1f}" font-family="{family}" font-size="{size}" '
        f'font-weight="{weight}" fill="{fill}" text-anchor="{anchor}" '
        f'opacity="{opacity}"{extra}>{esc(s)}</text>'
    )


def mono(x, y, s, size=13, fill="#c9d1d9", weight="normal", anchor="start"):
    return text(x, y, s, size, fill, weight, anchor,
                family="'DejaVu Sans Mono', 'Consolas', monospace")


def rect(x, y, w, h, fill, rx=10, stroke="none", sw=1, opacity=1.0, extra=""):
    return (
        f'<rect x="{x:.1f}" y="{y:.1f}" width="{w:.1f}" height="{h:.1f}" rx="{rx}" '
        f'fill="{fill}" stroke="{stroke}" stroke-width="{sw}" opacity="{opacity}"{extra}/>'
    )


def truncate(s, n):
    s = str(s)
    return s if len(s) <= n else s[: n - 1] + "…"


def arc_path(cx, cy, r_out, r_in, a0, a1):
    """Donut segment between angles a0, a1 (degrees, 0 = 12 o'clock)."""
    def pt(r, a):
        rad = math.radians(a - 90)
        return cx + r * math.cos(rad), cy + r * math.sin(rad)

    large = 1 if (a1 - a0) % 360 > 180 else 0
    x0, y0 = pt(r_out, a0)
    x1, y1 = pt(r_out, a1)
    x2, y2 = pt(r_in, a1)
    x3, y3 = pt(r_in, a0)
    return (
        f"M {x0:.2f} {y0:.2f} A {r_out} {r_out} 0 {large} 1 {x1:.2f} {y1:.2f} "
        f"L {x2:.2f} {y2:.2f} A {r_in} {r_in} 0 {large} 0 {x3:.2f} {y3:.2f} Z"
    )


def stacked_bar(x, y, w, h, parts, rx=4):
    """parts: [(value, colour)]; returns svg for a proportional stacked bar."""
    total = sum(v for v, _ in parts) or 1
    out = [rect(x, y, w, h, "#161b22", rx=rx)]
    cx = x
    for v, colour in parts:
        if v <= 0:
            continue
        seg = w * v / total
        out.append(rect(cx, y, max(seg, 0.6), h, colour, rx=0))
        cx += seg
    out.append(rect(x, y, w, h, "none", rx=rx, stroke="#30363d", sw=1))
    return "".join(out)


# ---------------------------------------------------------------------------
# The dependency graph
# ---------------------------------------------------------------------------


def graph_layout(data):
    nodes = {n["file"]: dict(n) for n in data["graph"]["nodes"]}
    edges = data["graph"]["edges"]
    layers = defaultdict(list)
    for n in nodes.values():
        layers[n["depth"]].append(n["file"])
    for d in layers:
        layers[d].sort()
    # barycentre ordering: pull each node towards the nodes it depends on
    below = defaultdict(list)
    for e in edges:
        below[e["from"]].append(e["to"])
    for _ in range(6):
        pos = {}
        for d in sorted(layers):
            for i, f in enumerate(layers[d]):
                pos[f] = i
        for d in sorted(layers)[1:]:
            def key(f):
                ns = [pos[t] for t in below[f] if t in pos]
                return (sum(ns) / len(ns)) if ns else pos[f]
            layers[d].sort(key=key)
    return layers, nodes, edges


NODE_W, NODE_H, COL_GAP, ROW_GAP = 232, 62, 22, 78


def render_dependency_svg(data, path):
    layers, nodes, edges = graph_layout(data)
    depths = sorted(layers)
    ncols = max(len(layers[d]) for d in depths)
    width = ncols * (NODE_W + COL_GAP) + COL_GAP + 40
    top = 150
    height = top + len(depths) * (NODE_H + ROW_GAP) + 150
    xy = {}
    for row, d in enumerate(reversed(depths)):  # deepest dependencies at the bottom
        fs = layers[d]
        row_w = len(fs) * (NODE_W + COL_GAP) - COL_GAP
        x0 = (width - row_w) / 2
        y = top + row * (NODE_H + ROW_GAP)
        for i, f in enumerate(fs):
            xy[f] = (x0 + i * (NODE_W + COL_GAP), y)

    out = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" '
        f'viewBox="0 0 {width} {height}" font-family="\'DejaVu Sans\', sans-serif">',
        "<defs>"
        '<linearGradient id="bg" x1="0" y1="0" x2="0" y2="1">'
        '<stop offset="0%" stop-color="#0d1117"/><stop offset="100%" stop-color="#12182100"/>'
        "</linearGradient>"
        '<marker id="arrow" markerWidth="9" markerHeight="9" refX="8" refY="3" orient="auto">'
        '<path d="M0,0 L0,6 L8,3 z" fill="#484f58"/></marker>'
        "</defs>",
        rect(0, 0, width, height, "#0d1117", rx=0),
        text(40, 58, "Dependency graph of the Lean development", 30, "#f0f6fc", "bold"),
        text(40, 88,
             "Each box is a module; an arrow A → B means a declaration in A uses a declaration in B "
             "(kernel-level, from the compiled environment).",
             15, "#8b949e"),
        text(40, 112,
             "Arrow thickness = number of declaration-level uses.  The bar in each box is the module's "
             "source mix: DASHI · Wikidata · original.",
             15, "#8b949e"),
    ]

    # edges first
    for e in edges:
        if e["from"] not in xy or e["to"] not in xy:
            continue
        x1, y1 = xy[e["from"]]
        x2, y2 = xy[e["to"]]
        sx, sy = x1 + NODE_W / 2, y1 + NODE_H
        tx, ty = x2 + NODE_W / 2, y2
        w = min(5.0, 0.5 + math.log1p(e["weight"]) * 0.9)
        opacity = 0.25 + min(0.5, e["weight"] / 120.0)
        my = (sy + ty) / 2
        out.append(
            f'<path d="M {sx:.1f} {sy:.1f} C {sx:.1f} {my:.1f} {tx:.1f} {my:.1f} {tx:.1f} {ty:.1f}" '
            f'fill="none" stroke="#484f58" stroke-width="{w:.2f}" opacity="{opacity:.2f}" '
            f'marker-end="url(#arrow)"/>'
        )

    for f, (x, y) in xy.items():
        n = nodes[f]
        mix = n["by_source"]
        dominant = max(SOURCES, key=lambda s: mix[s])
        colour = SOURCES[dominant]["colour"]
        out.append(rect(x, y, NODE_W, NODE_H, "#161b22", rx=10, stroke=colour, sw=1.6))
        out.append(rect(x, y, 5, NODE_H, colour, rx=2))
        short = f[: -len(".lean")]
        out.append(text(x + 14, y + 22, truncate(short, 30), 14, "#e6edf3", "bold"))
        out.append(
            stacked_bar(
                x + 14, y + 30, NODE_W - 74, 9,
                [(mix[s], SOURCES[s]["colour"]) for s in SOURCES],
            )
        )
        out.append(
            text(x + NODE_W - 14, y + 38, f"{n['declarations']}", 13, "#8b949e", anchor="end")
        )
        parts = " · ".join(f"{mix[s]}" for s in SOURCES)
        out.append(text(x + 14, y + 53, f"dashi {mix['dashi']} · wiki {mix['wikidata']} · own {mix['original']}",
                        11, "#6e7681"))

    # legend + layer note
    ly = height - 110
    out.append(text(40, ly, "Legend", 16, "#f0f6fc", "bold"))
    lx = 40
    for s in SOURCES:
        out.append(rect(lx, ly + 12, 16, 16, SOURCES[s]["colour"], rx=4))
        out.append(text(lx + 24, ly + 25, SOURCES[s]["label"], 14, "#c9d1d9"))
        lx += 30 + 9 * len(SOURCES[s]["label"])
    out.append(
        text(40, ly + 56,
             f"{len(nodes)} modules · {len(edges)} module-to-module edges · "
             f"{data['totals']['dependency_edges']} declaration-level uses · "
             f"longest dependency chain: {max(depths) + 1} modules.  "
             "Rows are dependency depth: the bottom row depends on nothing else in the project.",
             14, "#8b949e"))
    out.append("</svg>")
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("\n".join(out))


def write_dot(data, path):
    lines = ["digraph provenance {", "  rankdir=BT;", "  node [shape=box, style=rounded];"]
    for n in data["graph"]["nodes"]:
        mix = n["by_source"]
        dominant = max(SOURCES, key=lambda s: mix[s])
        label = "%s\\n%d decls (dashi %d / wiki %d / own %d)" % (
            n["file"][: -len(".lean")], n["declarations"], mix["dashi"], mix["wikidata"], mix["original"])
        lines.append(
            '  "%s" [label="%s", color="%s"];'
            % (n["file"], label, SOURCES[dominant]["colour"])
        )
    for e in data["graph"]["edges"]:
        lines.append('  "%s" -> "%s" [label="%d", penwidth=%.2f];'
                     % (e["from"], e["to"], e["weight"], min(5.0, 0.5 + math.log1p(e["weight"]))))
    lines.append("}")
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("\n".join(lines) + "\n")


# ---------------------------------------------------------------------------
# The eleven bridge invariants (parsed from RELATED_WORK.md §1.2)
# ---------------------------------------------------------------------------


def bridge_invariants():
    path = os.path.join(ROOT, "RELATED_WORK.md")
    rows = []
    if not os.path.exists(path):
        return rows
    with open(path, encoding="utf-8") as fh:
        text_ = fh.read()
    start = text_.find("## 1.")
    end = text_.find("## 2.")
    for line in text_[start:end].split("\n"):
        if not line.startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) != 3 or not cells[0].isdigit():
            continue
        dissolved = cells[2].lower().startswith("*dissolved")
        rows.append(
            {
                "n": int(cells[0]),
                "invariant": cells[1],
                "rendering": cells[2],
                "status": "dissolved by porting" if dissolved else "proved here",
                "declarations": _names_in(cells[2]),
            }
        )
    return rows


# ---------------------------------------------------------------------------
# The DASHI infographic
# ---------------------------------------------------------------------------


def card(x, y, w, h, title=None, subtitle=None, accent="#30363d"):
    out = [
        rect(x, y, w, h, "#0f151d", rx=16, stroke=accent, sw=1.2),
        rect(x, y, w, 4, accent, rx=2),
    ]
    if title:
        out.append(text(x + 24, y + 40, title, 21, "#f0f6fc", "bold"))
    if subtitle:
        out.append(text(x + 24, y + 64, subtitle, 13.5, "#8b949e"))
    return out


def render_dashi_svg(data, path):
    T = data["totals"]
    mix = T["by_source"]
    total = T["declarations"]
    W = 1460
    parts = []
    y = 0

    # ---------------- header ----------------
    H = 210
    parts.append(
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{{HEIGHT}}" '
        f'viewBox="0 0 {W} {{HEIGHT}}" font-family="\'DejaVu Sans\', \'Segoe UI\', sans-serif">'
    )
    parts.append(
        "<defs>"
        '<linearGradient id="hdr" x1="0" y1="0" x2="1" y2="1">'
        '<stop offset="0%" stop-color="#161b22"/><stop offset="55%" stop-color="#1b2430"/>'
        '<stop offset="100%" stop-color="#12181f"/></linearGradient>'
        '<linearGradient id="shine" x1="0" y1="0" x2="1" y2="0">'
        '<stop offset="0%" stop-color="#f0883e" stop-opacity="0"/>'
        '<stop offset="50%" stop-color="#ffd7a8" stop-opacity="0.85"/>'
        '<stop offset="100%" stop-color="#f0883e" stop-opacity="0"/>'
        '<animateTransform attributeName="gradientTransform" type="translate" '
        'from="-1 0" to="1 0" dur="6s" repeatCount="indefinite"/>'
        "</linearGradient>"
        '<filter id="glow"><feGaussianBlur stdDeviation="6" result="b"/>'
        '<feMerge><feMergeNode in="b"/><feMergeNode in="SourceGraphic"/></feMerge></filter>'
        "</defs>"
    )
    parts.append(rect(0, 0, W, 10000, "#0d1117", rx=0))
    parts.append(rect(0, 0, W, H, "url(#hdr)", rx=0))
    parts.append(rect(0, H - 4, W, 4, "url(#shine)", rx=0))
    parts.append(text(48, 74, "Where it comes from", 44, "#f0f6fc", "bold", extra=' filter="url(#glow)"'))
    parts.append(
        text(48, 106,
             "A provenance map of the Lean 4 Wikidata port: what is taken from the DASHI Agda bridge "
             "(chboishabba/dashi_agda PR #555 / #581 / #582),",
             15.5, "#adbac7"))
    parts.append(
        text(48, 128, "what comes from the Wikidata data model and standards, and what this port adds itself.",
             15.5, "#adbac7"))
    pills = [
        (f"{mix['dashi']} items traced to DASHI", SOURCES["dashi"]["colour"]),
        (f"{mix['wikidata']} items from the Wikidata model", SOURCES["wikidata"]["colour"]),
        (f"{mix['original']} items original here", SOURCES["original"]["colour"]),
        (f"{T['declarations']} declarations · {T['theorems']} theorems", "#8b949e"),
        ("0 sorry · standard axioms", "#8b949e"),
    ]
    px = 48
    for label, colour in pills:
        w = 20 + 8.0 * len(label)
        parts.append(rect(px, 148, w, 34, "#0d1117", rx=17, stroke=colour, sw=1.3))
        parts.append(rect(px + 12, 162, 7, 7, colour, rx=4))
        parts.append(text(px + 26, 170, label, 13.5, "#c9d1d9"))
        px += w + 12
    y = H + 26

    # ---------------- panel 1: donut + stats ----------------
    ph = 330
    parts += card(40, y, 470, ph, "Source mix of every declaration",
                  f"{total} declarations across {T['modules_with_declarations']} modules",
                  SOURCES["dashi"]["colour"])
    cx, cy = 175, y + 195
    a = 0.0
    for s in SOURCES:
        v = mix[s]
        if v == 0:
            continue
        sweep = 360.0 * v / total
        parts.append(
            f'<path d="{arc_path(cx, cy, 96, 58, a, a + sweep)}" fill="{SOURCES[s]["colour"]}" '
            f'stroke="#0d1117" stroke-width="2"/>'
        )
        mid = a + sweep / 2
        rad = math.radians(mid - 90)
        lx, ly = cx + 122 * math.cos(rad), cy + 122 * math.sin(rad)
        parts.append(text(lx, ly, f"{100.0 * v / total:.0f}%", 15, "#e6edf3", "bold", anchor="middle"))
        a += sweep
    parts.append(text(cx, cy - 4, str(total), 30, "#f0f6fc", "bold", anchor="middle"))
    parts.append(text(cx, cy + 18, "items", 13, "#8b949e", anchor="middle"))
    short_labels = {"dashi": "DASHI bridge", "wikidata": "Wikidata model",
                    "original": "Original here"}
    lx, ly = 300, y + 132
    for s in SOURCES:
        parts.append(rect(lx, ly - 12, 14, 14, SOURCES[s]["colour"], rx=4))
        parts.append(text(lx + 22, ly, short_labels[s], 14, "#c9d1d9", "bold"))
        parts.append(text(lx + 22, ly + 19, f"{mix[s]} items", 12, "#8b949e"))
        parts.append(text(lx + 22, ly + 35,
                          f"{T['theorems_by_source'][s]} thm · {T['definitions_by_source'][s]} def",
                          12, "#6e7681"))
        ly += 62

    stats = [
        (str(mix["dashi"]), "declarations traced to the bridge", SOURCES["dashi"]["colour"]),
        (f"{100.0 * mix['dashi'] / total:.0f}%", "of all items, by count", SOURCES["dashi"]["colour"]),
        (str(data["dashi_modules"]), f"of {T['modules_with_declarations']} modules carry DASHI content", "#d29922"),
        (str(T["theorems_by_source"]["dashi"]), "theorems rendering a bridge idea", "#f0883e"),
        ("9 / 11", "bridge invariants proved here (2 dissolved)", "#3fb950"),
        (f"{T['items_needing']['dashi']}", "items that transitively need a DASHI item", "#f0883e"),
    ]
    sx0, sy0, sw, sh = 540, y, 285, 105
    for i, (big, label, colour) in enumerate(stats):
        gx = sx0 + (i % 3) * (sw + 15)
        gy = sy0 + (i // 3) * (sh + 15)
        parts.append(rect(gx, gy, sw, sh, "#0f151d", rx=14, stroke="#21262d", sw=1.2))
        parts.append(rect(gx, gy, 4, sh, colour, rx=2))
        parts.append(text(gx + 20, gy + 52, big, 34, colour, "bold"))
        parts.append(text(gx + 20, gy + 78, label, 12.5, "#8b949e"))
    y += ph + 26

    # ---------------- panel 2: what needs what ----------------
    ph = 400
    parts += card(40, y, W - 80, ph, "How many items need which source",
                  "For every declaration, the transitive set of project declarations its proof or definition depends on "
                  "(from the compiled kernel environment), classified by source.",
                  "#d29922")
    by = y + 100
    for s in SOURCES:
        v = T["items_needing"][s]
        frac = v / total
        parts.append(text(64, by + 14, SOURCES[s]["label"], 14, "#c9d1d9"))
        parts.append(rect(430, by, W - 640, 22, "#161b22", rx=6))
        parts.append(rect(430, by, (W - 640) * frac, 22, SOURCES[s]["colour"], rx=6))
        parts.append(text(W - 200, by + 16, f"{v} items · {100 * frac:.0f}%", 14, "#e6edf3", "bold"))
        by += 40
    buckets = data["dashi_share_buckets"]
    parts.append(text(64, by + 40, "…and how much of an item's support is bridge-derived",
                      15, "#e6edf3", "bold"))
    bx, bw = 64, (W - 200) / len(buckets)
    bmax = max(buckets.values()) or 1
    for label, v in buckets.items():
        h = 74.0 * v / bmax
        parts.append(rect(bx, by + 150 - h, bw - 26, h, SOURCES["dashi"]["colour"], rx=5,
                          opacity=0.35 if label in ("none", "no support set") else 0.95))
        parts.append(text(bx + (bw - 26) / 2, by + 143 - h, str(v), 13, "#e6edf3", "bold",
                          anchor="middle"))
        parts.append(text(bx + (bw - 26) / 2, by + 168, label, 12.5, "#8b949e", anchor="middle"))
        bx += bw
    parts.append(
        text(64, by + 196,
             f"Median support set: {data['median_support']} declarations · "
             f"largest: {data['max_support']} · {T['dependency_edges']} direct uses in total · "
             f"longest module chain: {data['longest_chain']} modules.",
             13, "#8b949e"))
    y += ph + 26

    # ---------------- panel 3: per-module DASHI content ----------------
    rows = [m for m in data["modules"] if m["by_source"]["dashi"] > 0]
    rows.sort(key=lambda m: -m["by_source"]["dashi"])
    ph = 150 + math.ceil(len(rows) / 2) * 26
    parts += card(40, y, W - 80, ph, "DASHI content, module by module",
                  "Bar = the module's whole source mix; the number is how many of its declarations are traced to the bridge.",
                  SOURCES["dashi"]["colour"])
    colw = (W - 110) / 2
    for i, m in enumerate(rows):
        col, row = i % 2, i // 2
        x = 56 + col * colw
        ry = y + 108 + row * 26
        parts.append(text(x, ry, truncate(m["module"].replace("RequestProject.", ""), 34), 13, "#c9d1d9"))
        parts.append(stacked_bar(x + 240, ry - 12, colw - 425, 15,
                                 [(m["by_source"][s], SOURCES[s]["colour"]) for s in SOURCES]))
        parts.append(text(x + colw - 165, ry, f"{m['by_source']['dashi']} / {m['declarations']}",
                          13, SOURCES["dashi"]["colour"], "bold"))
        parts.append(text(x + colw - 95, ry, f"{m['needs_dashi_items']} need", 12, "#6e7681"))
    y += ph + 26

    # ---------------- panel 4: most load-bearing DASHI ideas ----------------
    impact = data["dashi_impact"][:12]
    ph = 140 + len(impact) * 30
    parts += card(40, y, W - 80, ph, "The load-bearing DASHI ideas",
                  "Traced declarations ranked by how many declarations in the project transitively depend on them.",
                  "#f0883e")
    hy = y + 100
    parts.append(text(64, hy, "declaration", 12, "#6e7681"))
    parts.append(text(500, hy, "module", 12, "#6e7681"))
    parts.append(text(760, hy, "used by", 12, "#6e7681"))
    parts.append(text(850, hy, "idea in the bridge", 12, "#6e7681"))
    for i, r in enumerate(impact):
        ry = hy + 28 + i * 30
        if i % 2 == 0:
            parts.append(rect(56, ry - 18, W - 112, 26, "#11171f", rx=6))
        parts.append(mono(64, ry, truncate(r["name"], 44), 13, "#e6edf3"))
        parts.append(text(500, ry, truncate(r["module"].replace("RequestProject.", ""), 28), 12.5, "#8b949e"))
        parts.append(text(790, ry, str(r["used_by"]), 13, SOURCES["dashi"]["colour"], "bold", anchor="end"))
        parts.append(text(850, ry, truncate(re.sub(r"`", "", r["upstream"]), 72), 12.5, "#adbac7"))
    y += ph + 26

    # ---------------- panel 5: the eleven invariants ----------------
    inv = data["invariants"]
    ph = 130 + len(inv) * 34
    parts += card(40, y, W - 80, ph, "The eleven bridge invariants, and where each one lives now",
                  "Transcribed from the bridge's own invariant list; the right-hand column is the Lean declaration that carries it.",
                  "#3fb950")
    hy = y + 100
    for i, r in enumerate(inv):
        ry = hy + i * 34
        if i % 2 == 0:
            parts.append(rect(56, ry - 18, W - 112, 30, "#11171f", rx=6))
        colour = "#3fb950" if r["status"] == "proved here" else "#8b949e"
        parts.append(text(70, ry, str(r["n"]), 13, "#6e7681"))
        parts.append(text(96, ry, truncate(r["invariant"], 66), 13, "#c9d1d9"))
        parts.append(rect(640, ry - 14, 118, 22, "#0d1117", rx=11, stroke=colour, sw=1.1))
        parts.append(text(699, ry + 1, r["status"], 11.5, colour, anchor="middle"))
        names = ", ".join(r["declarations"][:3]) or "—"
        parts.append(mono(775, ry, truncate(names, 78), 12, "#adbac7"))
    y += ph + 26

    # ---------------- footer ----------------
    ph = 212
    parts += card(40, y, W - 80, ph, "How these numbers are made", None, "#30363d")
    notes = [
        "Declarations are parsed from the Lean sources; dependencies are read off the compiled kernel environment "
        "(tools/DepDump.lean), so the graph is what the proofs really use.",
        "A declaration counts as DASHI-traced when the porting notes name it in an upstream correspondence row "
        "(PORTING_NOTES.md tables, RELATED_WORK.md §1) — the attribution is auditable, not guessed.",
        "It counts as Wikidata when it lives in a data-model module and states Wikidata vocabulary "
        "(property/item ids, rank, truthy, statements, RDF, constraints, identifiers); otherwise it is original to this port.",
        "The counts are also carried in Lean as a machine-checked ledger: RequestProject/Meta/Provenance.lean.",
        "The module dependency graph is the companion figure, docs/status/dependencies.svg; "
        "the full tables are in docs/status/PROVENANCE.md and docs/status/provenance.json.",
        "Refresh:  lake env lean tools/DepDump.lean  &&  python3 tools/provenance.py",
    ]
    for i, n in enumerate(notes):
        parts.append(text(64, y + 78 + i * 22, n, 12.5, "#8b949e"))
    y += ph + 30

    svg = "\n".join(parts).replace("{HEIGHT}", str(int(y)))
    svg += "\n</svg>\n"
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(svg)


# ---------------------------------------------------------------------------
# The written report
# ---------------------------------------------------------------------------


def pct(v, total):
    return f"{100.0 * v / total:.0f}%" if total else "0%"


def write_markdown(data, path):
    T = data["totals"]
    total = T["declarations"]
    L = []
    A = L.append
    A("# Provenance and dependency report")
    A("")
    A("Where every declaration in this Lean development comes from, what depends on")
    A("what, and how much of each item's support comes from which source.")
    A("")
    A("Generated by `tools/provenance.py` from the Lean sources and from the compiled")
    A("kernel environment (`tools/DepDump.lean`).  Companion figures:")
    A("`docs/status/dashi.svg` (the DASHI provenance infographic) and")
    A("`docs/status/dependencies.svg` (the dependency graph).")
    A("")
    A("## 0. How a declaration is attributed")
    A("")
    A("| source | rule |")
    A("| --- | --- |")
    A("| **DASHI Agda bridge (PR #555 / #581 / #582)** | the declaration is named in an upstream "
      "correspondence row of `PORTING_NOTES.md` or of `RELATED_WORK.md` §1 — i.e. the notes "
      "state that it renders an idea of the bridge |")
    A("| **Wikidata data model & standards** | not DASHI-traced, lives in a Wikidata "
      "data-model module, and states Wikidata vocabulary (item/property ids, rank, truthy, "
      "statements, RDF, constraints, identifiers, provenance) |")
    A("| **Original to this Lean port** | everything else: the executable engines, their "
      "exactness theorems, the generic epistemic machinery and the countermodels |")
    A("")
    A("\"Declarations\" here are the named top-level declarations of the sources")
    A("(`theorem`, `lemma`, `def`, `abbrev`, `structure`, `inductive`, named `instance`);")
    A("anonymous instances and the auxiliary constants the compiler generates are not")
    A("counted as items, though they are followed through when computing dependencies.")
    A("")
    A("The attribution is *auditable*: each DASHI row in §5 below carries the upstream idea")
    A("it was traced to, and the in-source `-- @source` comments carry the same text next to")
    A("the declaration itself.")
    A("")
    A("## 1. The source mix")
    A("")
    A("| source | declarations | share | theorems | definitions |")
    A("| --- | ---: | ---: | ---: | ---: |")
    for s in SOURCES:
        A("| %s | %d | %s | %d | %d |" % (
            SOURCES[s]["label"], T["by_source"][s], pct(T["by_source"][s], total),
            T["theorems_by_source"][s], T["definitions_by_source"][s]))
    A("| **total** | **%d** | 100%% | **%d** | **%d** |" % (total, T["theorems"], T["definitions"]))
    A("")
    A("%d modules, %d lines of Lean, %d declaration-level uses inside the project."
      % (T["modules"], T["lines"], T["dependency_edges"]))
    A("")
    A("(`RequestProject/Meta/Provenance.lean` is generated *from* this analysis and is")
    A("therefore not part of it.)")
    A("")
    A("## 2. Module by module")
    A("")
    A("`needs DASHI` counts the declarations of the module whose transitive support")
    A("contains at least one bridge-traced declaration.")
    A("")
    A("| module | lines | decls | thm | DASHI | Wikidata | original | needs DASHI |")
    A("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |")
    for m in sorted(data["modules"], key=lambda m: -m["by_source"]["dashi"]):
        if m["declarations"] == 0:
            continue
        A("| `%s` | %d | %d | %d | %d | %d | %d | %d |" % (
            m["module"], m["lines"], m["declarations"], m["theorems"],
            m["by_source"]["dashi"], m["by_source"]["wikidata"], m["by_source"]["original"],
            m["needs_dashi_items"]))
    A("")
    A("## 3. How many items need which source")
    A("")
    A("For each declaration, take the transitive set of project declarations it uses")
    A("(kernel-level).  Then:")
    A("")
    A("| source | items whose support contains it | share of all %d items |" % total)
    A("| --- | ---: | ---: |")
    for s in SOURCES:
        A("| %s | %d | %s |" % (SOURCES[s]["label"], T["items_needing"][s],
                                pct(T["items_needing"][s], total)))
    A("")
    A("Median support set: %d declarations; largest: %d; longest module chain: %d modules."
      % (data["median_support"], data["max_support"], data["longest_chain"]))
    A("")
    A("### How much of an item's support is bridge-derived")
    A("")
    A("| share of the support set traced to DASHI | declarations |")
    A("| --- | ---: |")
    for label, v in data["dashi_share_buckets"].items():
        A("| %s | %d |" % (label, v))
    A("")
    A("### Which modules need which source")
    A("")
    A("Declarations of the module whose transitive support contains at least one item")
    A("of each source (a module's own declarations count too).")
    A("")
    A("| module | decls | need DASHI | need Wikidata | need original |")
    A("| --- | ---: | ---: | ---: | ---: |")
    for m in sorted(data["modules"], key=lambda m: -m["needs_items"]["dashi"]
                    if m["declarations"] else 0):
        if m["declarations"] == 0:
            continue
        A("| `%s` | %d | %d | %d | %d |" % (
            m["module"].replace("RequestProject.", ""), m["declarations"],
            m["needs_items"]["dashi"], m["needs_items"]["wikidata"],
            m["needs_items"]["original"]))
    A("")
    A("### The load-bearing DASHI ideas")
    A("")
    A("| declaration | module | items depending on it | idea in the bridge |")
    A("| --- | --- | ---: | --- |")
    for r in data["dashi_impact"][:15]:
        A("| `%s` | `%s` | %d | %s |" % (r["name"], r["module"], r["used_by"],
                                         r["upstream"].replace("|", "\\|")))
    A("")
    A("## 4. The dependency graph")
    A("")
    A("%d modules carry declarations; there are %d module-to-module edges."
      % (T["modules_with_declarations"], T["module_edges"]))
    A("Rendered in `docs/status/dependencies.svg` (and `dependencies.dot` for Graphviz).")
    A("The same graph is carried in Lean, with its acyclicity proved, in")
    A("`RequestProject/Meta/Provenance.lean`.")
    A("")
    A("### Dependency depth")
    A("")
    A("Depth 0 modules depend on nothing else in the project; a module at depth *n* has a")
    A("chain of *n* project modules below it.")
    A("")
    A("| depth | modules |")
    A("| ---: | --- |")
    bydepth = defaultdict(list)
    for n in data["graph"]["nodes"]:
        bydepth[n["depth"]].append(n["file"][: -len(".lean")])
    for d in sorted(bydepth):
        A("| %d | %s |" % (d, ", ".join("`%s`" % x for x in sorted(bydepth[d]))))
    A("")
    A("### Heaviest edges")
    A("")
    A("| module | uses | declaration-level uses |")
    A("| --- | --- | ---: |")
    for e in data["graph"]["edges"][:20]:
        A("| `%s` | `%s` | %d |" % (e["from"][: -5], e["to"][: -5], e["weight"]))
    A("")
    A("## 5. Every declaration traced to the DASHI bridge")
    A("")
    A("| declaration | module | kind | idea in the bridge |")
    A("| --- | --- | --- | --- |")
    for r in sorted((r for r in data["declarations"] if r["source"] == "dashi"),
                    key=lambda r: (r["file"], r["line"])):
        A("| `%s` | `%s` | %s | %s |" % (
            r["name"], r["module"].replace("RequestProject.", ""), r["kind"],
            r["upstream"].replace("|", "\\|")))
    A("")
    A("## 6. The eleven bridge invariants")
    A("")
    A("| # | invariant (source wording, abridged) | status here | declarations |")
    A("| ---: | --- | --- | --- |")
    for r in data["invariants"]:
        A("| %d | %s | %s | %s |" % (
            r["n"], r["invariant"].replace("|", "\\|"), r["status"],
            ", ".join("`%s`" % n for n in r["declarations"][:4]) or "—"))
    A("")
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("\n".join(L))


# ---------------------------------------------------------------------------
# The machine-checked Lean ledger
# ---------------------------------------------------------------------------

LEDGER_HEADER = '''import Mathlib

/-!
# The provenance ledger, machine-checked

This module is **generated** by `tools/provenance.py` from the Lean sources and
from the compiled kernel environment (`tools/DepDump.lean`).  It carries, as
data inside Lean, the numbers that the provenance report and the infographic
state informally:

* for every module of the development, how many of its declarations are traced
  to the DASHI Agda bridge (`chboishabba/dashi_agda` PR #555 / #581 / #582), how many
  render the Wikidata data model, and how many are original to this port;
* the module dependency graph, as it really is in the compiled environment.

The arithmetic claims are then *theorems* (`by decide`), so the ledger cannot
silently disagree with itself, and the dependency graph is proved acyclic.

Regenerate with

```
lake env lean tools/DepDump.lean && python3 tools/provenance.py
```
-/

-- The ledger's `decide` goals fold over the whole development, so the default
-- recursion depth is not enough once the ledger grows.
set_option maxRecDepth 40000

namespace RequestProject.Meta

/-- Where a declaration came from. -/
inductive Src
  | /-- Traced to the DASHI Agda bridge. -/ dashi
  | /-- The Wikidata data model and the standards around it. -/ wikidata
  | /-- Introduced by this Lean port. -/ original
  deriving DecidableEq, Repr

/-- The provenance record of one module: its position in a topological order of
the dependency graph, its declaration counts, and its source mix. -/
structure ModuleProvenance where
  /-- Index of the module in the topological order used by `depEdges`. -/
  index : Nat
  /-- Fully qualified module name. -/
  name : String
  /-- Number of source declarations in the module. -/
  declarations : Nat
  /-- How many of them are theorems. -/
  theorems : Nat
  /-- How many are traced to the DASHI bridge. -/
  dashi : Nat
  /-- How many render the Wikidata data model. -/
  wikidata : Nat
  /-- How many are original to this port. -/
  original : Nat
  deriving DecidableEq, Repr

'''

LEDGER_FOOTER = '''
/-- Total number of declarations recorded in the ledger. -/
def totalDeclarations : Nat := (ledger.map (·.declarations)).sum

/-- Declarations attributed to a given source. -/
def totalFor : Src → Nat
  | .dashi => (ledger.map (·.dashi)).sum
  | .wikidata => (ledger.map (·.wikidata)).sum
  | .original => (ledger.map (·.original)).sum

/-- The modules that carry at least one bridge-traced declaration. -/
def dashiModules : List ModuleProvenance := ledger.filter (fun m => 0 < m.dashi)

/-- One module uses another: `(a, b) ∈ depEdges` means some declaration of the
module with index `a` uses a declaration of the module with index `b`. -/
def Uses (a b : Nat) : Prop := (a, b) ∈ depEdges

instance (a b : Nat) : Decidable (Uses a b) := inferInstanceAs (Decidable (_ ∈ _))

/-- The ledger is indexed by position: `index` really is the position in the list. -/
theorem ledger_index_eq : ledger.map (·.index) = List.range ledger.length := by decide

/-- Every module's source mix accounts for all of its declarations. -/
theorem module_mix_total : ∀ m ∈ ledger, m.dashi + m.wikidata + m.original = m.declarations := by
  decide

/-- The three sources partition the development. -/
theorem sources_partition :
    totalFor .dashi + totalFor .wikidata + totalFor .original = totalDeclarations := by
  decide

/-- Every dependency edge points from a module to one that is strictly earlier in
the topological order.  This is the ledger's copy of "the graph is layered". -/
theorem depEdges_decreasing : ∀ e ∈ depEdges, e.2 < e.1 := by decide

/-- Both endpoints of every edge are modules of the ledger. -/
theorem depEdges_mem : ∀ e ∈ depEdges, e.1 < ledger.length ∧ e.2 < ledger.length := by decide

/-- A chain of uses strictly decreases the topological index. -/
theorem lt_of_transGen_uses {a b : Nat} (h : Relation.TransGen Uses a b) : b < a := by
  induction h with
  | single hab => exact depEdges_decreasing _ hab
  | tail _ hbc ih => exact lt_trans (depEdges_decreasing _ hbc) ih

/-- **The dependency graph of the development is acyclic.** -/
theorem uses_acyclic (a : Nat) : ¬ Relation.TransGen Uses a a := fun h =>
  absurd (lt_of_transGen_uses h) (lt_irrefl a)

/-- No module uses itself. -/
theorem uses_irrefl (a : Nat) : ¬ Uses a a := fun h => uses_acyclic a (.single h)

/-- The bridge-traced declarations, by fully qualified name.  Each of these is
named in an upstream correspondence row of `PORTING_NOTES.md` or
`RELATED_WORK.md` §1, and carries an `-- @source` comment in its own module. -/
def dashiTraced : List String := [
{DASHI_NAMES}
]

/-- The name list and the per-module counts agree. -/
theorem dashiTraced_length : dashiTraced.length = totalFor .dashi := by decide

end RequestProject.Meta
'''


def write_lean_ledger(data, path):
    nodes = {n["file"]: n for n in data["graph"]["nodes"]}
    order = data["graph"]["topological_order"]
    index = {f: i for i, f in enumerate(order)}
    mods = {m["file"]: m for m in data["modules"]}
    rows = []
    for f in order:
        m = mods[f]
        rows.append(
            "  { index := %d, name := \"%s\", declarations := %d, theorems := %d,\n"
            "    dashi := %d, wikidata := %d, original := %d }"
            % (index[f], m["module"], m["declarations"], m["theorems"],
               m["by_source"]["dashi"], m["by_source"]["wikidata"], m["by_source"]["original"])
        )
    edges = sorted(
        {(index[e["from"]], index[e["to"]]) for e in data["graph"]["edges"]
         if e["from"] in index and e["to"] in index}
    )
    bad = [e for e in edges if not e[1] < e[0]]
    if bad:
        raise SystemExit("topological order is not a topological order: %r" % bad[:5])
    edge_lines = []
    for i in range(0, len(edges), 6):
        edge_lines.append(
            "  " + ", ".join("(%d, %d)" % e for e in edges[i : i + 6]) + ","
        )
    edge_block = "\n".join(edge_lines).rstrip(",")
    names = sorted(r["name"] for r in data["declarations"] if r["source"] == "dashi")
    name_block = ",\n".join('  "%s"' % n for n in names)

    body = [
        LEDGER_HEADER,
        "/-- One record per module of the development, in topological order:\n"
        "a module only uses modules that appear before it. -/\n"
        "def ledger : List ModuleProvenance := [\n"
        + ",\n".join(rows)
        + "\n]\n",
        "/-- The module dependency graph: `(a, b)` means a declaration of module `a`\n"
        "uses a declaration of module `b`.  Read off the compiled environment. -/\n"
        "def depEdges : List (Nat × Nat) := [\n" + edge_block + "\n]\n",
        LEDGER_FOOTER.replace("{DASHI_NAMES}", name_block),
    ]
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write("\n".join(body))


# ---------------------------------------------------------------------------
# In-source attribution comments
# ---------------------------------------------------------------------------

GEN_BLOCK_START = "/-! ### Provenance (generated by `tools/provenance.py`)"


def _insertion_point(lines, decl_line):
    """Index (0-based) at which to put the @source line for a declaration.

    Walks back over the declaration's own docstring and attribute lines.
    """
    i = decl_line - 1  # 0-based index of the declaration line
    while i > 0:
        prev = lines[i - 1].strip()
        if prev.startswith("@["):
            i -= 1
            continue
        if prev.endswith("-/") and not prev.startswith("/-!"):
            j = i - 1
            while j > 0 and not lines[j].lstrip().startswith("/--"):
                j -= 1
            if lines[j].lstrip().startswith("/--"):
                i = j
                continue
        break
    return i


def annotate_sources(data):
    """Write `-- @source ...` lines and the per-module provenance block."""
    per_file = defaultdict(list)
    for r in data["declarations"]:
        per_file[r["file"]].append(r)
    mods = {m["file"]: m for m in data["modules"]}
    touched = 0
    for rel in lean_files():
        path = os.path.join(SRC, rel)
        with open(path, encoding="utf-8") as fh:
            lines = fh.read().split("\n")
        # 1. drop the previous generated annotations
        lines = [ln for ln in lines if not SOURCE_TAG_RE.match(ln)]
        out = []
        skipping = False
        for ln in lines:
            if ln.startswith(GEN_BLOCK_START):
                skipping = True
            if skipping:
                if ln.rstrip().endswith("-/"):
                    skipping = False
                continue
            out.append(ln)
        while len(out) > 1 and out[0].strip() == "":
            out.pop(0)
        lines = out
        # 2. recompute declaration positions on the cleaned file
        with open(path, "w", encoding="utf-8") as fh:
            fh.write("\n".join(lines))
        _imports, decls = parse_file(rel)
        upstream = {r["name"]: r for r in per_file[rel]}
        # 3. insert the @source lines, bottom-up
        for d in sorted(decls, key=lambda d: -d.line):
            r = upstream.get(d.name)
            if r is None or r["source"] != "dashi":
                continue
            idea = re.sub(r"\s+", " ", r["upstream"]).strip()
            idea = truncate(idea, 96)
            at = _insertion_point(lines, d.line)
            indent = lines[d.line - 1][: len(lines[d.line - 1]) - len(lines[d.line - 1].lstrip())]
            lines.insert(at, f"{indent}-- @source DASHI Agda bridge (PR #555/#581/#582): {idea}")
            touched += 1
        # 4. the module provenance block, after the module docstring
        m = mods[rel]
        if m["declarations"] > 0:
            mix = m["by_source"]
            block = [
                GEN_BLOCK_START,
                "",
                "Source mix of this module's %d declarations: %d traced to the DASHI Agda"
                % (m["declarations"], mix["dashi"]),
                "bridge (`chboishabba/dashi_agda` PR #555 / #581 / #582), %d rendering the Wikidata"
                % mix["wikidata"],
                "data model, %d original to this port.  The bridge-traced declarations are"
                % mix["original"],
                "marked with `-- @source` below.  Full ledger: `docs/status/PROVENANCE.md`.",
                "-/",
                "",
            ]
            pos = 0
            for i, ln in enumerate(lines):
                if ln.startswith("/-!"):
                    j = i
                    while j < len(lines) and not lines[j].rstrip().endswith("-/"):
                        j += 1
                    pos = min(j + 1, len(lines))
                    break
                if ln.startswith("import"):
                    pos = i + 1
            while pos < len(lines) and lines[pos].strip() == "":
                pos += 1
            while pos >= 2 and lines[pos - 1].strip() == "" and lines[pos - 2].strip() == "":
                del lines[pos - 1]
                pos -= 1
            lines[pos:pos] = block
        with open(path, "w", encoding="utf-8") as fh:
            fh.write("\n".join(lines))
    return touched


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def main(argv):
    os.makedirs(OUT_DIR, exist_ok=True)
    data = analyse()
    if "--annotate" in argv:
        n = annotate_sources(data)
        print("annotated %d declarations in the Lean sources" % n)
        data = analyse()  # line numbers moved
    with open(os.path.join(OUT_DIR, "provenance.json"), "w", encoding="utf-8") as fh:
        json.dump(data, fh, indent=1, sort_keys=False)
        fh.write("\n")
    write_markdown(data, os.path.join(OUT_DIR, "PROVENANCE.md"))
    write_dot(data, os.path.join(OUT_DIR, "dependencies.dot"))
    render_dependency_svg(data, os.path.join(OUT_DIR, "dependencies.svg"))
    render_dashi_svg(data, os.path.join(OUT_DIR, "dashi.svg"))
    write_lean_ledger(data, os.path.join(SRC, "Meta", "Provenance.lean"))
    try:
        import cairosvg

        for name, width in (("dependencies", 1900), ("dashi", 1460)):
            cairosvg.svg2png(
                url=os.path.join(OUT_DIR, name + ".svg"),
                write_to=os.path.join(OUT_DIR, name + ".png"),
                output_width=width,
            )
    except Exception as exc:  # pragma: no cover - PNG is a convenience
        print("PNG rendering skipped (%s)" % exc)
    T = data["totals"]
    print(
        "%d declarations: %d DASHI · %d Wikidata · %d original; %d module edges"
        % (T["declarations"], T["by_source"]["dashi"], T["by_source"]["wikidata"],
           T["by_source"]["original"], T["module_edges"])
    )


if __name__ == "__main__":
    main(sys.argv[1:])
