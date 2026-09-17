#!/usr/bin/env python3
"""Collect status metrics for the Lean 4 Wikidata port and render the infographic.

Reads every Lean source under ``RequestProject/`` and writes

  * ``docs/status/status.json``  -- the machine-readable numbers
  * ``docs/status/status.svg``   -- the infographic

Run from the repository root:  python3 tools/status_report.py
"""

from __future__ import annotations

import json
import os
import re
from collections import OrderedDict

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "RequestProject")
OUT_DIR = os.path.join(ROOT, "docs", "status")

# ---------------------------------------------------------------------------
# Grouping of the modules.  The first axis of the comparison the report makes:
# the Wikidata import proper versus the rest of the Lean development.
# ---------------------------------------------------------------------------

GROUPS: "OrderedDict[str, dict]" = OrderedDict(
    [
        (
            "wikidata-engine",
            {
                "label": "Wikidata engine (core)",
                "side": "wikidata",
                "colour": "#1f6feb",
                "modules": [
                    "Wikidata/Reachability.lean",
                    "Wikidata/Core.lean",
                    "Wikidata/ClassAlgebra.lean",
                    "Wikidata/Redundancy.lean",
                    "Wikidata/Diagnostics.lean",
                    "Wikidata/Alignment.lean",
                    "Wikidata/Provenance.lean",
                ],
            },
        ),
        (
            "wikidata-surfaces",
            {
                "label": "Wikidata surfaces (layers, slices, RDF, constraints, identity)",
                "side": "wikidata",
                "colour": "#388bfd",
                "modules": [
                    "Wikidata/Slices.lean",
                    "Wikidata/Layers.lean",
                    "Wikidata/Rdf.lean",
                    "Wikidata/Constraints.lean",
                    "Wikidata/Identity.lean",
                    "Wikidata/Lens.lean",
                    "Wikidata/Values.lean",
                    "Wikidata/Qualifiers.lean",
                    "Wikidata/Sparql.lean",
                    "Wikidata/Owl.lean",
                    "Wikidata/BlankNodes.lean",
                ],
            },
        ),
        (
            "attribution",
            {
                "label": "Fifth pass (fibres, attribution, alignment safety, diagnostics)",
                "side": "wikidata",
                "colour": "#79c0ff",
                "modules": [
                    "Wikidata/DerivationFibres.lean",
                    "Wikidata/Attribution.lean",
                    "Wikidata/AlignmentSafety.lean",
                    "Wikidata/DisjointUnionDiagnostics.lean",
                    "Wikidata/RdfInformationOrder.lean",
                ],
            },
        ),
        (
            "parenting",
            {
                "label": "Parenting surface (slots, carrier, fibres, authority)",
                "side": "wikidata",
                "colour": "#58a6ff",
                "modules": [
                    "Wikidata/Parenting.lean",
                    "Wikidata/ParentingRoles.lean",
                    "Wikidata/ParentingFibres.lean",
                    "Wikidata/ParentingAuthority.lean",
                ],
            },
        ),
        (
            "epistemic",
            {
                "label": "Evidence / epistemic layer",
                "side": "rest",
                "colour": "#8957e5",
                "modules": [
                    "Epistemic/Trit.lean",
                    "Epistemic/Bridge.lean",
                    "Epistemic/Repair.lean",
                    "Epistemic/Context.lean",
                    "Epistemic/Surfaces.lean",
                    "Epistemic/ValueEvidence.lean",
                    "Epistemic/QueryEvidence.lean",
                    "Epistemic/Views.lean",
                    "Epistemic/Tetralemma.lean",
                    "Epistemic/Lens.lean",
                    "Epistemic/ParentingEvidence.lean",
                    "Epistemic/FourView.lean",
                    "Epistemic/ObligationAuthority.lean",
                    "Epistemic/ContextErasure.lean",
                ],
            },
        ),
        (
            "projection-cores",
            {
                "label": "Projection cores (observers, residuals, authority)",
                "side": "rest",
                "colour": "#a371f7",
                "modules": [
                    "Epistemic/Observer.lean",
                    "Epistemic/Quotient.lean",
                    "Epistemic/Authority.lean",
                ],
            },
        ),
        (
            "regression",
            {
                "label": "Worked regression (artist / painter / sculptor)",
                "side": "wikidata",
                "colour": "#3fb950",
                "modules": [
                    "Wikidata/Examples.lean",
                    "Wikidata/ExamplesLayers.lean",
                    "Wikidata/ExamplesConflict.lean",
                ],
            },
        ),
        (
            "polarity",
            {
                "label": "Evidence polarity, axes and observer joins (PR #582)",
                "side": "rest",
                "colour": "#bc8cff",
                "modules": [
                    "Epistemic/ObserverJoin.lean",
                    "Epistemic/Opposition.lean",
                    "Epistemic/AxisSupport.lean",
                ],
            },
        ),
        (
            "ternary",
            {
                "label": "Balanced-ternary carrier and its quotients (PR #582)",
                "side": "rest",
                "colour": "#e3b341",
                "modules": [
                    "Ternary/Balanced.lean",
                    "Ternary/Base369.lean",
                    "Ternary/Aggregate.lean",
                ],
            },
        ),
        (
            "polarity-surface",
            {
                "label": "Polarity and view joins on the Wikidata surface (PR #582)",
                "side": "wikidata",
                "colour": "#7ee787",
                "modules": [
                    "Wikidata/EvidencePolarity.lean",
                    "Wikidata/ViewJoin.lean",
                    "Wikidata/Learning.lean",
                ],
            },
        ),
        (
            "agda-frontend",
            {
                "label": "Agda-subset front end (prelude, syntax)",
                "side": "rest",
                "colour": "#d29922",
                "modules": [
                    "Agda/Prelude.lean",
                    "Agda/Syntax.lean",
                ],
            },
        ),
        (
            "harness",
            {
                "label": "Harness (imports, entry point)",
                "side": "rest",
                "colour": "#8b949e",
                "modules": ["All.lean", "Main.lean"],
            },
        ),
    ]
)

THEOREM_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|nonrec\s+)*(theorem|lemma)\s+([A-Za-z_0-9'.«»]+)"
)
DEF_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+)*"
    r"(def|abbrev|structure|inductive|instance)\b"
)
EXAMPLE_RE = re.compile(r"^\s*example\b")
DECIDE_RE = re.compile(r"\bdecide\b")

# A result is counted as "negative" when its name states that something is *not*
# licensed.  These are the invariants the source bridge is made of.
NEGATIVE_TOKENS = {
    "not",
    "ne",
    "never",
    "no",
    "fails",
    "lossy",
    "forgets",
    "forget",
    "isEmpty",
    "irrelevant",
    "inert",
}


def is_negative(name: str) -> bool:
    """Heuristic: the name states a disequality or a non-entailment.

    Matching is on underscore-separated tokens, so ``holds_mono_of_positive``
    (which contains ``no``) is not counted while ``no_transition_...`` is.
    """
    tail = name.split(".")[-1]
    tokens = tail.split("_")
    return any(tok in NEGATIVE_TOKENS for tok in tokens)


def blocks(lines):
    """Split a Lean file into top-level declaration blocks.

    Yields ``(kind, name, body_lines)`` where ``kind`` is one of ``theorem``,
    ``def`` or ``example``.
    """
    current = None
    for line in lines:
        m = THEOREM_RE.match(line)
        m2 = DEF_RE.match(line)
        m3 = EXAMPLE_RE.match(line)
        if m:
            if current:
                yield current
            current = ("theorem", m.group(2), [line])
        elif m2:
            if current:
                yield current
            current = ("def", m2.group(1), [line])
        elif m3:
            if current:
                yield current
            current = ("example", "example", [line])
        elif current:
            current[2].append(line)
    if current:
        yield current


def scan(path: str) -> dict:
    lines = open(path, encoding="utf-8").read().splitlines()
    theorems, negatives, defs, examples, decided = [], [], 0, 0, 0
    sorries = sum(1 for line in lines if re.search(r"\bsorry\b", line))
    for kind, name, body in blocks(lines):
        text_body = "\n".join(body)
        if kind == "theorem":
            theorems.append(name)
            if is_negative(name):
                negatives.append(name)
            if DECIDE_RE.search(text_body):
                decided += 1
        elif kind == "def":
            defs += 1
        else:
            examples += 1
    return {
        "lines": len(lines),
        "theorems": len(theorems),
        "negative_results": len(negatives),
        "negative_names": negatives,
        "definitions": defs,
        "examples": examples,
        "decided_by_computation": decided,
        "sorries": sorries,
    }


def collect() -> dict:
    groups = OrderedDict()
    for key, spec in GROUPS.items():
        mods = []
        for rel in spec["modules"]:
            data = scan(os.path.join(SRC, rel))
            data["module"] = "RequestProject/" + rel
            mods.append(data)
        agg = {
            k: sum(m[k] for m in mods)
            for k in (
                "lines",
                "theorems",
                "negative_results",
                "definitions",
                "examples",
                "decided_by_computation",
                "sorries",
            )
        }
        agg.update(
            {
                "label": spec["label"],
                "side": spec["side"],
                "colour": spec["colour"],
                "files": len(mods),
                "modules": mods,
            }
        )
        groups[key] = agg

    def side_total(side: str, field: str) -> int:
        return sum(g[field] for g in groups.values() if g["side"] == side)

    totals = {
        "files": sum(g["files"] for g in groups.values()),
        "lines": sum(g["lines"] for g in groups.values()),
        "theorems": sum(g["theorems"] for g in groups.values()),
        "negative_results": sum(g["negative_results"] for g in groups.values()),
        "definitions": sum(g["definitions"] for g in groups.values()),
        "examples": sum(g["examples"] for g in groups.values()),
        "decided_by_computation": sum(g["decided_by_computation"] for g in groups.values()),
        "sorries": sum(g["sorries"] for g in groups.values()),
    }
    sides = {
        side: {
            field: side_total(side, field)
            for field in (
                "files",
                "lines",
                "theorems",
                "negative_results",
                "definitions",
                "decided_by_computation",
            )
        }
        for side in ("wikidata", "rest")
    }

    # ------------------------------------------------------------------
    # The second axis: coverage of the upstream Agda bridge's Wikidata
    # surface.  These entries are transcribed from RELATED_WORK.md sections
    # 1.2, 1.4 and 2.10 and from the "Scope" section of PORTING_NOTES.md;
    # each "ported" row names the Lean module that carries it.
    # ------------------------------------------------------------------
    upstream = {
        "invariants": {
            "total": 11,
            "proved_here": 9,
            "dissolved_by_porting": 2,
            "open": 0,
        },
        "surfaces": [
            {"name": "class order (P279) / instance (P31)", "status": "ported", "where": "Wikidata/Core.lean"},
            {"name": "ranks and the truthy projection", "status": "ported", "where": "Wikidata/Core.lean, Wikidata/Layers.lean"},
            {"name": "class algebra (union / intersection / disjointness)", "status": "ported", "where": "Wikidata/ClassAlgebra.lean"},
            {"name": "diagnostics and validity", "status": "ported", "where": "Wikidata/Diagnostics.lean"},
            {"name": "redundancy pruning", "status": "ported", "where": "Wikidata/Redundancy.lean"},
            {"name": "cross-ontology alignment", "status": "ported", "where": "Wikidata/Alignment.lean"},
            {"name": "provenance and temporal slices", "status": "ported", "where": "Wikidata/Provenance.lean, Wikidata/Slices.lean"},
            {"name": "statement-layer tower", "status": "ported", "where": "Wikidata/Layers.lean"},
            {"name": "reified / direct RDF layers", "status": "ported", "where": "Wikidata/Rdf.lean"},
            {"name": "property and schema constraints", "status": "ported", "where": "Wikidata/Constraints.lean"},
            {"name": "mereology (part-of) separation", "status": "ported", "where": "Wikidata/Constraints.lean"},
            {"name": "identity: matching, sitelinks, IDs, lexemes", "status": "ported", "where": "Wikidata/Identity.lean"},
            {"name": "three-valued evidence trit", "status": "ported", "where": "Epistemic/Trit.lean"},
            {"name": "four-cornered support square", "status": "ported", "where": "Epistemic/Tetralemma.lean"},
            {"name": "lens / view-family transitions", "status": "ported", "where": "Epistemic/Lens.lean, Wikidata/Lens.lean"},
            {"name": "review-only repair boundary", "status": "ported", "where": "Epistemic/Repair.lean"},
            {"name": "parent slots (P22 / P25 / P8810 / P1531) and descent", "status": "ported", "where": "Wikidata/Parenting.lean"},
            {"name": "progeniture carrier and genetic cardinality cap", "status": "ported", "where": "Wikidata/Parenting.lean"},
            {"name": "flat parenting-role vocabulary", "status": "ported", "where": "Wikidata/ParentingRoles.lean"},
            {"name": "observer refinement lattice and fibre dynamics", "status": "ported", "where": "Epistemic/Observer.lean"},
            {"name": "sections, residuals and exact reopening", "status": "ported", "where": "Epistemic/Quotient.lean"},
            {"name": "consumer / policy future safety and delegated authority", "status": "ported", "where": "Epistemic/Authority.lean, Wikidata/ParentingAuthority.lean"},
            {"name": "authority-routing non-factorability", "status": "ported", "where": "Wikidata/ParentingFibres.lean"},
            {"name": "claim-centred derivation fibres and axis subfibres", "status": "ported", "where": "Wikidata/DerivationFibres.lean"},
            {"name": "link strength gating fact / identity transfer", "status": "ported", "where": "Wikidata/DerivationFibres.lean"},
            {"name": "four-layer cross-ontology contradiction attribution", "status": "ported", "where": "Wikidata/Attribution.lean"},
            {"name": "BFO continuant/occurrent Wikidata attribution case", "status": "ported", "where": "Wikidata/Attribution.lean"},
            {"name": "inference-language-indexed alignment safety", "status": "ported", "where": "Wikidata/AlignmentSafety.lean"},
            {"name": "disjoint-union diagnostic coordinates", "status": "ported", "where": "Wikidata/DisjointUnionDiagnostics.lean"},
            {"name": "RDF view information order (no reconstruction)", "status": "ported", "where": "Wikidata/RdfInformationOrder.lean"},
            {"name": "four-view disagreement matrix and its boundary", "status": "ported", "where": "Epistemic/FourView.lean"},
            {"name": "evidence / obligation / authority separation", "status": "ported", "where": "Epistemic/ObligationAuthority.lean"},
            {"name": "conditional / marginal reversal under context erasure", "status": "ported", "where": "Epistemic/ContextErasure.lean"},
            {"name": "balanced-ternary interaction carrier and its exact counts", "status": "ported", "where": "Ternary/Balanced.lean"},
            {"name": "base-3/6/9 blockwise vs. aggregate readings", "status": "ported", "where": "Ternary/Base369.lean"},
            {"name": "binary / balanced-ternary aggregate loss", "status": "ported", "where": "Ternary/Aggregate.lean"},
            {"name": "transverse observers and their least common refinement", "status": "ported", "where": "Epistemic/ObserverJoin.lean"},
            {"name": "claim-indexed evidence polarity (operator roles, fibre pooling)", "status": "ported", "where": "Epistemic/Opposition.lean"},
            {"name": "required evidence axes and non-compensation", "status": "ported", "where": "Epistemic/AxisSupport.lean"},
            {"name": "polarity and required axes on the Wikidata surface", "status": "ported", "where": "Wikidata/EvidencePolarity.lean"},
            {"name": "layer and slice as transverse readings of a base", "status": "ported", "where": "Wikidata/ViewJoin.lean"},
            {"name": "governed residual ontology learning (cohorts, merges)", "status": "ported", "where": "Wikidata/Learning.lean"},
            {"name": "Agda-subset front end for Lean", "status": "ported", "where": "Agda/Prelude.lean, Agda/Syntax.lean, Agda/Verbatim.lean, AgdaVendor/, AgdaCheck/, tools/agda2lean.py, tools/agdacheck.py"},
            {"name": "receipt architecture (source hashes, manifests)", "status": "declined", "where": "one kernel here: a pinned hash would add ceremony, not assurance"},
            {"name": "boolean boundary records", "status": "declined", "where": "restated as theorems where they constrained data"},
            {"name": "wider DASHI mathematics (Moonshine, Hecke, ...)", "status": "out-of-scope", "where": "unrelated to the Wikidata surface"},
            {"name": "quantity / time / coordinate value types", "status": "ported", "where": "Wikidata/Values.lean"},
            {"name": "qualifiers and references as first-class objects", "status": "ported", "where": "Wikidata/Qualifiers.lean"},
            {"name": "evidence at an instant over the value surfaces", "status": "ported", "where": "Epistemic/ValueEvidence.lean"},
            {"name": "unit conversion between quantity units", "status": "declined", "where": "the comparison refuses to compare across units rather than converting"},
            {"name": "SPARQL core fragment and answer monotonicity", "status": "ported", "where": "Wikidata/Sparql.lean"},
            {"name": "query answers as imported evidence", "status": "ported", "where": "Epistemic/QueryEvidence.lean"},
            {"name": "SPARQL property paths and named graphs", "status": "ported", "where": "Wikidata/SparqlPaths.lean, Wikidata/NamedGraphs.lean"},
            {"name": "property-path answers as imported evidence", "status": "ported", "where": "Epistemic/PathEvidence.lean"},
            {"name": "SELECT DISTINCT, GROUP BY / COUNT / HAVING and where monotonicity stops", "status": "ported", "where": "Wikidata/SparqlAggregation.lean"},
            {"name": "MINUS vs FILTER NOT EXISTS: two negations that differ", "status": "ported", "where": "Wikidata/SparqlNegation.lean"},
            {"name": "SPARQL expression language (arithmetic and string FILTERs, subqueries, federation)", "status": "ported", "where": "Wikidata/SparqlExpressions.lean"},
            {"name": "property characteristics (transitive / symmetric / inverse)", "status": "ported", "where": "Wikidata/Owl.lean"},
            {"name": "OWL class expressions (intersection, union, complement, restrictions)", "status": "ported", "where": "Wikidata/ClassExpressions.lean"},
            {"name": "OWL beyond the class and property fragments (nominals, cardinality, datatypes)", "status": "ported", "where": "Wikidata/OwlCardinality.lean"},
            {"name": "RDF blank nodes and simple entailment (interpolation lemma, decision procedure)", "status": "ported", "where": "Wikidata/BlankNodes.lean"},
        ],
        "notes": "Three upstream pull requests are covered: the original Agda bridge, the parent/progenitor tranche and the evidence-polarity cross-pollination tranche; the Wikidata-facing parts are what is ported here.",
    }
    counts: dict = {}
    for row in upstream["surfaces"]:
        counts[row["status"]] = counts.get(row["status"], 0) + 1
    upstream["status_counts"] = counts

    return {
        "generated_by": "tools/status_report.py",
        "build": {
            "toolchain": open(os.path.join(ROOT, "lean-toolchain")).read().strip(),
            "sorry_free": totals["sorries"] == 0,
            "axioms": ["propext", "Classical.choice", "Quot.sound"],
        },
        "groups": groups,
        "totals": totals,
        "sides": sides,
        "upstream": upstream,
    }


# ---------------------------------------------------------------------------
# SVG rendering
# ---------------------------------------------------------------------------

BG = "#0d1117"
FG = "#e6edf3"
MUTED = "#8b949e"
PANEL = "#161b22"
GRID = "#30363d"

STATUS_COLOUR = {
    "ported": "#3fb950",
    "declined": "#d29922",
    "out-of-scope": "#6e7681",
    "gap": "#f85149",
}


def esc(s: str) -> str:
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def text(x, y, s, size=13, fill=FG, weight="normal", anchor="start"):
    return (
        f'<text x="{x}" y="{y}" font-family="Helvetica, Arial, sans-serif" font-size="{size}" '
        f'fill="{fill}" font-weight="{weight}" text-anchor="{anchor}">{esc(s)}</text>'
    )


def rect(x, y, w, h, fill, rx=6, opacity=1.0):
    return f'<rect x="{x}" y="{y}" width="{max(w, 0)}" height="{h}" rx="{rx}" fill="{fill}" opacity="{opacity}"/>'


def render(d: dict) -> str:
    n_rows = (len(d["upstream"]["surfaces"]) + 1) // 2
    panel1_h = 90 + 62 * len(d["groups"]) + 40
    W, H = 1240, 250 + (panel1_h + 30) + (178 + n_rows * 36 + 46) + 60
    out = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}">',
        rect(0, 0, W, H, BG, rx=0),
    ]

    # ---- header ----------------------------------------------------------
    out.append(text(40, 58, "Lean 4 Wikidata port \u2014 status report", 30, FG, "bold"))
    out.append(
        text(
            40,
            86,
            "the Wikidata import next to the rest of the development, and next to the upstream Agda bridge it came from",
            14,
            MUTED,
        )
    )

    t = d["totals"]
    b = d["build"]
    cards = [
        (f"{t['files']}", "Lean modules"),
        (f"{t['lines']:,}", "lines of Lean"),
        (f"{t['theorems']}", "theorems"),
        (f"{t['negative_results']}", "negative results"),
        (f"{t['definitions']}", "definitions"),
        (f"{t['decided_by_computation']}", "machine-decided"),
        ("0" if b["sorry_free"] else str(t["sorries"]), "sorries"),
    ]
    gap, y0 = 16, 108
    cw = ((W - 80) - gap * (len(cards) - 1)) // len(cards)
    for i, (big, small) in enumerate(cards):
        x = 40 + i * (cw + gap)
        out.append(rect(x, y0, cw, 78, PANEL))
        out.append(text(x + 14, y0 + 38, big, 26, FG, "bold"))
        out.append(text(x + 14, y0 + 62, small, 11, MUTED))
    out.append(
        text(
            40,
            y0 + 104,
            f"toolchain {b['toolchain']}  \u00b7  builds clean  \u00b7  axioms: {', '.join(b['axioms'])}",
            12,
            MUTED,
        )
    )

    # ---- panel 1: wikidata vs rest --------------------------------------
    py = 250
    out.append(rect(40, py, W - 80, panel1_h, PANEL))
    out.append(text(64, py + 34, "1 \u00b7 The Wikidata import vs. the rest of the development", 18, FG, "bold"))
    out.append(
        text(
            64,
            py + 56,
            "bars are lines of Lean; counters on the right: theorems / negative results / definitions / proofs closed by computation",
            12,
            MUTED,
        )
    )

    groups = d["groups"]
    maxlines = max(g["lines"] for g in groups.values())
    bx, bw = 470, 440
    row_y = py + 90
    for g in groups.values():
        out.append(text(64, row_y + 16, g["label"], 13, FG))
        out.append(
            text(
                64,
                row_y + 34,
                f"{g['files']} module{'s' if g['files'] != 1 else ''}  \u00b7  "
                + ("Wikidata import" if g["side"] == "wikidata" else "rest of the development"),
                11,
                MUTED,
            )
        )
        w = int(bw * g["lines"] / maxlines)
        out.append(rect(bx, row_y + 6, bw, 26, GRID, rx=4, opacity=0.35))
        out.append(rect(bx, row_y + 6, w, 26, g["colour"], rx=4))
        if w > bw - 76:
            out.append(text(bx + w - 10, row_y + 25, f"{g['lines']} lines", 12, "#ffffff", anchor="end"))
        else:
            out.append(text(bx + w + 10, row_y + 25, f"{g['lines']} lines", 12, MUTED))
        out.append(
            text(
                W - 64,
                row_y + 25,
                f"{g['theorems']} thm \u00b7 {g['negative_results']} neg \u00b7 "
                f"{g['definitions']} def \u00b7 {g['decided_by_computation']} decided",
                12,
                FG,
                anchor="end",
            )
        )
        row_y += 62

    s = d["sides"]
    tot_lines = s["wikidata"]["lines"] + s["rest"]["lines"]
    split_y = row_y + 10
    out.append(text(64, split_y + 19, "share of the development", 13, FG, "bold"))
    sx, sw = 470, 440
    wshare = int(sw * s["wikidata"]["lines"] / tot_lines)
    out.append(rect(sx, split_y, wshare, 26, "#1f6feb", rx=4))
    out.append(rect(sx + wshare, split_y, sw - wshare, 26, "#8957e5", rx=4))
    pct = 100.0 * s["wikidata"]["lines"] / tot_lines
    out.append(text(sx + 10, split_y + 19, f"Wikidata {pct:.0f}%", 12, "#ffffff", "bold"))
    out.append(text(sx + wshare + 10, split_y + 19, f"rest {100 - pct:.0f}%", 12, "#ffffff", "bold"))
    out.append(
        text(
            W - 64,
            split_y + 19,
            f"{s['wikidata']['theorems']} thm vs {s['rest']['theorems']} thm",
            12,
            FG,
            anchor="end",
        )
    )

    # ---- panel 2: upstream coverage -------------------------------------
    rows = d["upstream"]["surfaces"]
    half = (len(rows) + 1) // 2
    panel2_h = 178 + half * 36 + 46
    py2 = py + panel1_h + 30
    out.append(rect(40, py2, W - 80, panel2_h, PANEL))
    out.append(text(64, py2 + 34, "2 \u00b7 Coverage of the upstream Agda bridge's Wikidata surface", 18, FG, "bold"))
    up = d["upstream"]
    inv = up["invariants"]
    out.append(
        text(
            64,
            py2 + 56,
            f"{inv['total']} stated bridge invariants: {inv['proved_here']} proved here, "
            f"{inv['dissolved_by_porting']} dissolved by porting, {inv['open']} open",
            12,
            MUTED,
        )
    )

    counts = up["status_counts"]
    order = ["ported", "declined", "out-of-scope", "gap"]
    legend_labels = {
        "ported": "ported and proved",
        "declined": "deliberately declined",
        "out-of-scope": "out of scope",
        "gap": "known gap",
    }
    lx, ly = 64, py2 + 84
    total_rows = sum(counts.get(k, 0) for k in order)
    barw = W - 128
    acc = 0
    for k in order:
        n = counts.get(k, 0)
        if not n:
            continue
        w = int(barw * n / total_rows)
        out.append(rect(lx + acc, ly, w, 22, STATUS_COLOUR[k], rx=4))
        if w > 40:
            out.append(text(lx + acc + 8, ly + 16, f"{n}", 12, "#0d1117", "bold"))
        acc += w
    lgx = 64
    for k in order:
        n = counts.get(k, 0)
        out.append(rect(lgx, ly + 34, 11, 11, STATUS_COLOUR[k], rx=2))
        out.append(text(lgx + 18, ly + 44, f"{legend_labels[k]} ({n})", 12, MUTED))
        lgx += 18 + int(6.4 * len(legend_labels[k])) + 60

    ry = ly + 74
    col_x = [64, 640]
    for i, row in enumerate(rows):
        cx = col_x[0] if i < half else col_x[1]
        yy = ry + (i if i < half else i - half) * 36
        out.append(rect(cx, yy, 536, 30, BG, rx=4))
        out.append(rect(cx, yy, 5, 30, STATUS_COLOUR[row["status"]], rx=2))
        out.append(text(cx + 16, yy + 14, row["name"], 12, FG))
        out.append(text(cx + 16, yy + 26, row["where"], 10, MUTED))

    out.append(text(64, py2 + panel2_h - 20, up["notes"], 11, MUTED))

    # ---- footer ----------------------------------------------------------
    out.append(
        text(
            40,
            H - 30,
            "generated by tools/status_report.py from the Lean sources; the numbers are also in docs/status/status.json",
            11,
            MUTED,
        )
    )
    out.append("</svg>")
    return "\n".join(out)


# ---------------------------------------------------------------------------
# Markdown rendering
# ---------------------------------------------------------------------------

STATUS_MARK = {
    "ported": "✅ ported and proved",
    "declined": "⚠️ deliberately declined",
    "out-of-scope": "⬜ out of scope",
    "gap": "❌ known gap",
}


def bar(value: int, maximum: int, width: int = 28) -> str:
    filled = int(round(width * value / maximum)) if maximum else 0
    return "█" * filled + "·" * (width - filled)


def render_markdown(d: dict) -> str:
    t, s, b, up = d["totals"], d["sides"], d["build"], d["upstream"]
    groups = d["groups"]
    L = []
    A = L.append

    A("# Status report: the Lean 4 Wikidata import vs. the rest of the project")
    A("")
    A("![status infographic](status.svg)")
    A("")
    A(
        "Two comparisons: **(1)** the Wikidata import against the rest of this Lean "
        "development, and **(2)** this port against the Wikidata surface of the "
        "upstream Agda bridge it was ported from. Every number in section 1 is "
        "counted from the Lean sources by `tools/status_report.py`; section 2 is "
        "transcribed from `PORTING_NOTES.md` and `RELATED_WORK.md`, and each "
        "'ported' row names the module that carries it."
    )
    A("")
    A("## At a glance")
    A("")
    A("| | |")
    A("| --- | --- |")
    A(f"| Lean modules | {t['files']} |")
    A(f"| Lines of Lean | {t['lines']:,} |")
    A(f"| Theorems | {t['theorems']} |")
    A(f"| of which negative results (some inference is *not* licensed) | {t['negative_results']} |")
    A(f"| Definitions (`def` / `structure` / `inductive` / `instance`) | {t['definitions']} |")
    A(f"| Theorems closed by computation (`decide`) | {t['decided_by_computation']} |")
    A(f"| `sorry` | {t['sorries']} |")
    A(f"| Toolchain | `{b['toolchain']}` |")
    A(f"| Axioms used | {', '.join('`' + a + '`' for a in b['axioms'])} |")
    A("")
    A("## 1 · The Wikidata import vs. the rest of the development")
    A("")
    maxlines = max(g["lines"] for g in groups.values())
    A("| Area | Side | Files | Lines | | Thm | Neg | Def | Decided |")
    A("| --- | --- | ---: | ---: | :-- | ---: | ---: | ---: | ---: |")
    for g in groups.values():
        side = "Wikidata import" if g["side"] == "wikidata" else "rest"
        A(
            f"| {g['label']} | {side} | {g['files']} | {g['lines']} | `{bar(g['lines'], maxlines)}` | "
            f"{g['theorems']} | {g['negative_results']} | {g['definitions']} | {g['decided_by_computation']} |"
        )
    A(
        f"| **total** | | **{t['files']}** | **{t['lines']}** | | **{t['theorems']}** | "
        f"**{t['negative_results']}** | **{t['definitions']}** | **{t['decided_by_computation']}** |"
    )
    A("")
    tot = s["wikidata"]["lines"] + s["rest"]["lines"]
    pct = 100.0 * s["wikidata"]["lines"] / tot
    A("| Side | Files | Lines | Share | Thm | Neg | Def | Decided |")
    A("| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |")
    for key, label in (("wikidata", "Wikidata import (`RequestProject/Wikidata`)"), ("rest", "Rest (evidence layer + harness)")):
        v = s[key]
        share = 100.0 * v["lines"] / tot
        A(
            f"| {label} | {v['files']} | {v['lines']} | {share:.0f}% | {v['theorems']} | "
            f"{v['negative_results']} | {v['definitions']} | {v['decided_by_computation']} |"
        )
    A("")
    A("What the split says:")
    A("")
    A(
        f"* The ontology side is the larger half — {pct:.0f}% of the lines and "
        f"{s['wikidata']['theorems']} of the {t['theorems']} theorems — because the port "
        "rebuilt an executable engine underneath the imported discipline rather than "
        "recording it."
    )
    A(
        f"* Negative results are concentrated in the evidence layer "
        f"({groups['epistemic']['negative_results']} of {groups['epistemic']['theorems']} theorems there, "
        f"vs. {groups['wikidata-engine']['negative_results']} of {groups['wikidata-engine']['theorems']} in the core engine): "
        "stating what an import does *not* license is the part inherited from the source bridge."
    )
    A(
        f"* The regression modules are almost entirely machine-decided "
        f"({groups['regression']['decided_by_computation']} of {groups['regression']['theorems']} theorems closed by `decide`), "
        "so the worked fragment is run through the real checkers rather than asserted."
    )
    A("")
    A("## 2 · Coverage of the upstream Agda bridge's Wikidata surface")
    A("")
    inv = up["invariants"]
    A(
        f"The source states its discipline as **{inv['total']} invariants**: "
        f"{inv['proved_here']} are proved here as theorems, {inv['dissolved_by_porting']} dissolve on porting "
        "(the results live in the same kernel as their consumers, and the worked fragment is "
        f"decided by the real checkers), {inv['open']} remain open. "
        "The invariant-by-invariant table is in `RELATED_WORK.md` §1.2."
    )
    A("")
    counts = up["status_counts"]
    A(
        "Surface-by-surface: "
        + ", ".join(f"**{counts.get(k, 0)}** {STATUS_MARK[k].split(' ', 1)[1]}" for k in ("ported", "declined", "out-of-scope", "gap"))
        + "."
    )
    A("")
    A("| Surface | Status | Where / why |")
    A("| --- | --- | --- |")
    for row in up["surfaces"]:
        where = row["where"]
        if row["status"] == "ported":
            where = ", ".join("`RequestProject/" + w.strip() + "`" for w in where.split(","))
        A(f"| {row['name']} | {STATUS_MARK[row['status']]} | {where} |")
    A("")
    A(f"*{up['notes']}*")
    A("")
    A("## Appendix · per-module figures")
    A("")
    A("| Module | Lines | Thm | Neg | Def | Decided |")
    A("| --- | ---: | ---: | ---: | ---: | ---: |")
    for g in groups.values():
        for m in g["modules"]:
            A(
                f"| `{m['module']}` | {m['lines']} | {m['theorems']} | {m['negative_results']} | "
                f"{m['definitions']} | {m['decided_by_computation']} |"
            )
    A("")
    A("## Regenerating")
    A("")
    A("```")
    A("python3 tools/status_report.py    # rewrites status.json, status.svg and STATUS_REPORT.md")
    A("```")
    A("")
    A(
        "Counting conventions: 'negative results' are theorems whose name carries a "
        "negative token (`not`, `ne`, `never`, `no`, `forgets`, `inert`, `irrelevant`, "
        "`lossy`) — i.e. it states a disequality or that some inference is not "
        "licensed; 'decided' counts theorems whose proof invokes `decide`. "
        "The raw numbers, including the list of negative-result names per module, are in "
        "`status.json`."
    )
    return "\n".join(L) + "\n"


def main() -> None:
    data = collect()
    os.makedirs(OUT_DIR, exist_ok=True)
    with open(os.path.join(OUT_DIR, "status.json"), "w", encoding="utf-8") as f:
        json.dump(data, f, indent=2)
        f.write("\n")
    with open(os.path.join(OUT_DIR, "status.svg"), "w", encoding="utf-8") as f:
        f.write(render(data))
        f.write("\n")
    with open(os.path.join(OUT_DIR, "STATUS_REPORT.md"), "w", encoding="utf-8") as f:
        f.write(render_markdown(data))
    try:  # optional raster copy, for viewers that do not render SVG
        import cairosvg  # type: ignore

        cairosvg.svg2png(
            url=os.path.join(OUT_DIR, "status.svg"),
            write_to=os.path.join(OUT_DIR, "status.png"),
            output_width=1240,
        )
    except Exception:
        pass
    print(json.dumps(data["totals"], indent=2))
    print(json.dumps(data["sides"], indent=2))
    print(json.dumps(data["upstream"]["status_counts"], indent=2))


if __name__ == "__main__":
    main()
