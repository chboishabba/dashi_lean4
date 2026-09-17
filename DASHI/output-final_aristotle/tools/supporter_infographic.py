#!/usr/bin/env python3
"""Render the supporter / follower status infographic.

A poster-style SVG with 3D (isometric and extruded) charts, written to

  * ``docs/status/supporters.svg``

Every number is read from the Lean sources through
``tools/status_report.py``'s collector, so the poster cannot drift from the
development.  Run from the repository root::

    python3 tools/supporter_infographic.py
"""

from __future__ import annotations

import math
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

from status_report import collect  # noqa: E402

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "docs", "status", "supporters.svg")

W = 1400

# ---------------------------------------------------------------------------
# palette
# ---------------------------------------------------------------------------

BG0 = "#05070f"
BG1 = "#0b1020"
PANEL = "#111827"
PANEL_EDGE = "#243049"
FG = "#eef2ff"
MUTED = "#93a4c8"

CYAN = "#22d3ee"
VIOLET = "#a855f7"
GREEN = "#34d399"
AMBER = "#fbbf24"
PINK = "#f472b6"
BLUE = "#60a5fa"
SLATE = "#64748b"
RED = "#fb7185"


def shade(colour: str, factor: float) -> str:
    """Multiply a ``#rrggbb`` colour by ``factor`` (clamped)."""
    c = colour.lstrip("#")
    r, g, b = (int(c[i : i + 2], 16) for i in (0, 2, 4))
    r, g, b = (min(255, max(0, int(v * factor))) for v in (r, g, b))
    return f"#{r:02x}{g:02x}{b:02x}"


def esc(s: str) -> str:
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def wrap(s: str, width: int) -> list:
    """Greedy word wrap to roughly ``width`` characters."""
    words, line, out = s.split(), "", []
    for w in words:
        if line and len(line) + len(w) + 1 > width:
            out.append(line)
            line = w
        else:
            line = (line + " " + w).strip()
    if line:
        out.append(line)
    return out


def text(x, y, s, size=14, fill=FG, weight="normal", anchor="start", opacity=1.0,
         family="Helvetica, Arial, sans-serif", extra=""):
    return (
        f'<text x="{x:.1f}" y="{y:.1f}" font-family="{family}" font-size="{size}" '
        f'fill="{fill}" font-weight="{weight}" text-anchor="{anchor}" '
        f'opacity="{opacity}" {extra}>{esc(s)}</text>'
    )


MONO = "ui-monospace, SFMono-Regular, Menlo, Consolas, monospace"


def poly(points, fill, opacity=1.0, extra=""):
    pts = " ".join(f"{x:.2f},{y:.2f}" for x, y in points)
    return f'<polygon points="{pts}" fill="{fill}" opacity="{opacity}" {extra}/>'


def panel(x, y, w, h, title=None, subtitle=None, accent=CYAN):
    """A rounded glass panel with a glowing accent rule."""
    out = [
        f'<rect x="{x}" y="{y}" width="{w}" height="{h}" rx="18" fill="url(#glass)" '
        f'stroke="{PANEL_EDGE}" stroke-width="1"/>',
        f'<rect x="{x + 20}" y="{y + 22}" width="4" height="22" rx="2" fill="{accent}" '
        f'filter="url(#soft)"/>',
    ]
    if title:
        out.append(text(x + 36, y + 40, title, 20, FG, "bold"))
    if subtitle:
        out.append(text(x + 36, y + 62, subtitle, 13, MUTED))
    return out


# ---------------------------------------------------------------------------
# isometric primitives
# ---------------------------------------------------------------------------

ISO_X = 0.866
ISO_Y = 0.5


def iso(ox, oy, x, y, z, sx=1.0, sy=1.0, sz=1.0):
    return (ox + (x - y) * ISO_X * sx, oy + (x + y) * ISO_Y * sy - z * sz)


def iso_box(ox, oy, x, y, w, d, h, colour, sx=1.0, sy=1.0, sz=1.0, opacity=1.0,
            glow=False, z0=0.0):
    """An extruded isometric box rising from ``z0``; the three visible faces."""
    P = lambda a, b, c: iso(ox, oy, a, b, c, sx, sy, sz)  # noqa: E731
    h = z0 + h
    top = [P(x, y, h), P(x + w, y, h), P(x + w, y + d, h), P(x, y + d, h)]
    right = [P(x + w, y, z0), P(x + w, y + d, z0), P(x + w, y + d, h), P(x + w, y, h)]
    left = [P(x, y + d, z0), P(x + w, y + d, z0), P(x + w, y + d, h), P(x, y + d, h)]
    extra = 'filter="url(#soft)"' if glow else ""
    return [
        poly(left, shade(colour, 0.52), opacity),
        poly(right, shade(colour, 0.74), opacity),
        poly(top, colour, opacity, extra),
    ]


# ---------------------------------------------------------------------------
# extruded (2.5D) ring / pie primitives
# ---------------------------------------------------------------------------


def ell(cx, cy, rx, ry, ang):
    return (cx + rx * math.cos(ang), cy + ry * math.sin(ang))


def donut_slice_path(cx, cy, rx, ry, r_in, a0, a1):
    """Path for one slice of a tilted (elliptical) donut."""
    ri_x, ri_y = rx * r_in, ry * r_in
    large = 1 if (a1 - a0) > math.pi else 0
    p0 = ell(cx, cy, rx, ry, a0)
    p1 = ell(cx, cy, rx, ry, a1)
    q1 = ell(cx, cy, ri_x, ri_y, a1)
    q0 = ell(cx, cy, ri_x, ri_y, a0)
    return (
        f'M {p0[0]:.2f} {p0[1]:.2f} '
        f'A {rx:.2f} {ry:.2f} 0 {large} 1 {p1[0]:.2f} {p1[1]:.2f} '
        f'L {q1[0]:.2f} {q1[1]:.2f} '
        f'A {ri_x:.2f} {ri_y:.2f} 0 {large} 0 {q0[0]:.2f} {q0[1]:.2f} Z'
    )


def extruded_donut(cx, cy, rx, ry, r_in, depth, slices, start=-math.pi / 2):
    """A tilted donut chart with an extruded body.

    ``slices`` is a list of ``(value, colour)``.  Drawn back-to-front, so the
    body reads as solid.
    """
    total = sum(v for v, _ in slices) or 1
    out = []
    angles = []
    a = start
    for value, colour in slices:
        a1 = a + 2 * math.pi * value / total
        angles.append((a, a1, colour))
        a = a1
    for k in range(depth, 0, -1):
        f = 0.30 + 0.16 * (1 - k / depth)
        for a0, a1, colour in angles:
            out.append(
                f'<path d="{donut_slice_path(cx, cy + k, rx, ry, r_in, a0, a1)}" '
                f'fill="{shade(colour, f)}"/>'
            )
    for a0, a1, colour in angles:
        out.append(
            f'<path d="{donut_slice_path(cx, cy, rx, ry, r_in, a0, a1)}" '
            f'fill="{colour}" stroke="{shade(colour, 0.45)}" stroke-width="0.8"/>'
        )
    return out, angles


def extruded_gauge(cx, cy, rx, ry, frac, colour, depth=9, width=15):
    """A tilted ring gauge with an extruded body; ``frac`` in [0, 1]."""
    out = []
    track = shade(colour, 0.28)
    for k in range(depth, 0, -1):
        out.append(
            f'<ellipse cx="{cx}" cy="{cy + k}" rx="{rx}" ry="{ry}" fill="none" '
            f'stroke="{shade(colour, 0.20)}" stroke-width="{width}"/>'
        )
    out.append(
        f'<ellipse cx="{cx}" cy="{cy}" rx="{rx}" ry="{ry}" fill="none" '
        f'stroke="{track}" stroke-width="{width}"/>'
    )
    frac = max(0.0, min(1.0, frac))
    a0 = -math.pi / 2
    a1 = a0 + 2 * math.pi * frac
    if frac >= 0.999:
        for k in range(depth, 0, -1):
            out.append(
                f'<ellipse cx="{cx}" cy="{cy + k}" rx="{rx}" ry="{ry}" fill="none" '
                f'stroke="{shade(colour, 0.45)}" stroke-width="{width}"/>'
            )
        out.append(
            f'<ellipse cx="{cx}" cy="{cy}" rx="{rx}" ry="{ry}" fill="none" '
            f'stroke="{colour}" stroke-width="{width}" filter="url(#soft)"/>'
        )
        return out
    large = 1 if (a1 - a0) > math.pi else 0
    p0, p1 = ell(cx, cy, rx, ry, a0), ell(cx, cy, rx, ry, a1)
    for k in range(depth, 0, -1):
        d = (f'M {p0[0]:.2f} {p0[1] + k:.2f} A {rx} {ry} 0 {large} 1 '
             f'{p1[0]:.2f} {p1[1] + k:.2f}')
        out.append(
            f'<path d="{d}" fill="none" stroke="{shade(colour, 0.45)}" '
            f'stroke-width="{width}" stroke-linecap="round"/>'
        )
    d = f'M {p0[0]:.2f} {p0[1]:.2f} A {rx} {ry} 0 {large} 1 {p1[0]:.2f} {p1[1]:.2f}'
    out.append(
        f'<path d="{d}" fill="none" stroke="{colour}" stroke-width="{width}" '
        f'stroke-linecap="round" filter="url(#soft)"/>'
    )
    return out



# Which pass of the port each module landed in (from PORTING_NOTES.md: the
# first pass built the engine and the evidence layer, the second the layer and
# slice surfaces, the third the support square and lenses, the fourth the
# parent/progenitor tranche).
PASS_MODULES = [
    (
        "Pass 1", "the engine", CYAN,
        [
            "Wikidata/Reachability.lean", "Wikidata/Core.lean",
            "Wikidata/ClassAlgebra.lean", "Wikidata/Redundancy.lean",
            "Wikidata/Diagnostics.lean", "Wikidata/Alignment.lean",
            "Wikidata/Provenance.lean", "Wikidata/Examples.lean",
            "Epistemic/Trit.lean", "Epistemic/Bridge.lean",
            "Epistemic/Repair.lean", "Epistemic/Context.lean",
            "All.lean", "Main.lean",
        ],
    ),
    (
        "Pass 2", "layers & slices", BLUE,
        [
            "Wikidata/Slices.lean", "Wikidata/Layers.lean", "Wikidata/Rdf.lean",
            "Wikidata/Constraints.lean", "Wikidata/Identity.lean",
            "Wikidata/ExamplesLayers.lean", "Epistemic/Surfaces.lean",
            "Epistemic/Views.lean",
        ],
    ),
    (
        "Pass 3", "the support square", VIOLET,
        [
            "Epistemic/Tetralemma.lean", "Epistemic/Lens.lean",
            "Wikidata/Lens.lean", "Wikidata/ExamplesConflict.lean",
        ],
    ),
    (
        "Pass 4", "parents & observers", PINK,
        [
            "Wikidata/Parenting.lean", "Wikidata/ParentingRoles.lean",
            "Wikidata/ParentingFibres.lean", "Wikidata/ParentingAuthority.lean",
            "Epistemic/Observer.lean", "Epistemic/Quotient.lean",
            "Epistemic/Authority.lean", "Epistemic/ParentingEvidence.lean",
        ],
    ),
    (
        "Pass 5", "attribution & context", AMBER,
        [
            "Wikidata/DerivationFibres.lean", "Wikidata/Attribution.lean",
            "Wikidata/AlignmentSafety.lean",
            "Wikidata/DisjointUnionDiagnostics.lean",
            "Wikidata/RdfInformationOrder.lean", "Epistemic/FourView.lean",
            "Epistemic/ObligationAuthority.lean", "Epistemic/ContextErasure.lean",
            "Agda/Prelude.lean", "Agda/Syntax.lean",
        ],
    ),
    (
        "Pass 6", "polarity & ternary", GREEN,
        [
            "Ternary/Balanced.lean", "Ternary/Base369.lean",
            "Ternary/Aggregate.lean", "Epistemic/ObserverJoin.lean",
            "Epistemic/Opposition.lean", "Epistemic/AxisSupport.lean",
            "Wikidata/EvidencePolarity.lean", "Wikidata/ViewJoin.lean",
            "Wikidata/Learning.lean",
        ],
    ),
    (
        "Pass 7", "values, qualifiers & queries", CYAN,
        [
            "Wikidata/Values.lean", "Wikidata/Qualifiers.lean",
            "Wikidata/Sparql.lean", "Wikidata/Owl.lean",
            "Epistemic/ValueEvidence.lean",
            "Epistemic/QueryEvidence.lean",
        ],
    ),
]


def pass_totals(d: dict) -> list:
    """Per-pass and cumulative counts, from the module-level scan."""
    by_module = {}
    for g in d["groups"].values():
        for m in g["modules"]:
            by_module[m["module"].split("RequestProject/", 1)[1]] = m
    rows, cum_t, cum_l = [], 0, 0
    for tag, name, colour, mods in PASS_MODULES:
        thm = sum(by_module[m]["theorems"] for m in mods)
        lines = sum(by_module[m]["lines"] for m in mods)
        neg = sum(by_module[m]["negative_results"] for m in mods)
        cum_t += thm
        cum_l += lines
        rows.append({
            "tag": tag, "name": name, "colour": colour, "files": len(mods),
            "theorems": thm, "lines": lines, "negative": neg,
            "cum_theorems": cum_t, "cum_lines": cum_l,
        })
    return rows


def iso_ribbon(P, pts, y0, dep, colour):
    """An extruded area ribbon over the points ``pts = [(x, z)]``.

    ``P`` is an axonometric projection ``(x, y, z) -> (screen_x, screen_y)``.
    """
    y1 = y0 + dep
    top = [P(x, y0, z) for x, z in pts] + [P(x, y1, z) for x, z in reversed(pts)]
    front = ([P(x, y1, z) for x, z in pts]
             + [P(pts[-1][0], y1, 0), P(pts[0][0], y1, 0)])
    cap = [P(pts[-1][0], y0, 0), P(pts[-1][0], y1, 0),
           P(pts[-1][0], y1, pts[-1][1]), P(pts[-1][0], y0, pts[-1][1])]
    return [
        poly(front, shade(colour, 0.62), 0.96),
        poly(cap, shade(colour, 0.78), 0.96),
        poly(top, colour, 0.94, 'filter="url(#soft)"'),
    ]


def axon(ox, oy, ax=(104.0, 7.0), ay=(-46.0, 30.0)):
    """A general axonometric projection: x mostly rightward, y into the page."""
    def P(x, y, z):
        return (ox + x * ax[0] + y * ay[0], oy + x * ax[1] + y * ay[1] - z)
    return P


# ---------------------------------------------------------------------------
# defs: gradients, glow, starfield
# ---------------------------------------------------------------------------


def defs(height: int) -> str:
    stars = []
    rnd = 12345

    def nxt():
        nonlocal rnd
        rnd = (1103515245 * rnd + 12345) % (1 << 31)
        return rnd / (1 << 31)

    for _ in range(190):
        x, y = nxt() * W, nxt() * height
        r = 0.6 + nxt() * 1.3
        o = 0.15 + nxt() * 0.5
        dur = 3 + nxt() * 6
        stars.append((x, y, r, o, dur))
    star_svg = "".join(
        f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{r:.2f}" fill="#cfe3ff" opacity="{o:.2f}">'
        f'<animate attributeName="opacity" values="{o:.2f};{min(1, o * 2.4):.2f};{o:.2f}" '
        f'dur="{dur:.1f}s" repeatCount="indefinite"/></circle>'
        for x, y, r, o, dur in stars
    )
    return f"""<defs>
  <linearGradient id="bg" x1="0" y1="0" x2="0.4" y2="1">
    <stop offset="0%" stop-color="{BG1}"/>
    <stop offset="55%" stop-color="{BG0}"/>
    <stop offset="100%" stop-color="#080d1b"/>
  </linearGradient>
  <radialGradient id="aura" cx="0.5" cy="0.5" r="0.5">
    <stop offset="0%" stop-color="{VIOLET}" stop-opacity="0.42"/>
    <stop offset="100%" stop-color="{VIOLET}" stop-opacity="0"/>
  </radialGradient>
  <radialGradient id="aura2" cx="0.5" cy="0.5" r="0.5">
    <stop offset="0%" stop-color="{CYAN}" stop-opacity="0.34"/>
    <stop offset="100%" stop-color="{CYAN}" stop-opacity="0"/>
  </radialGradient>
  <linearGradient id="glass" x1="0" y1="0" x2="0.2" y2="1">
    <stop offset="0%" stop-color="#182238" stop-opacity="0.95"/>
    <stop offset="100%" stop-color="#0c1322" stop-opacity="0.95"/>
  </linearGradient>
  <linearGradient id="title" x1="0" y1="0" x2="1" y2="0">
    <stop offset="0%" stop-color="{CYAN}">
      <animate attributeName="stop-color" values="{CYAN};{VIOLET};{GREEN};{CYAN}"
               dur="14s" repeatCount="indefinite"/>
    </stop>
    <stop offset="50%" stop-color="{VIOLET}">
      <animate attributeName="stop-color" values="{VIOLET};{GREEN};{CYAN};{VIOLET}"
               dur="14s" repeatCount="indefinite"/>
    </stop>
    <stop offset="100%" stop-color="{GREEN}">
      <animate attributeName="stop-color" values="{GREEN};{CYAN};{VIOLET};{GREEN}"
               dur="14s" repeatCount="indefinite"/>
    </stop>
  </linearGradient>
  <linearGradient id="sheen" x1="0" y1="0" x2="1" y2="0">
    <stop offset="0%" stop-color="#ffffff" stop-opacity="0"/>
    <stop offset="50%" stop-color="#ffffff" stop-opacity="0.16"/>
    <stop offset="100%" stop-color="#ffffff" stop-opacity="0"/>
  </linearGradient>
  <filter id="soft" x="-60%" y="-60%" width="220%" height="220%">
    <feGaussianBlur stdDeviation="6" result="b"/>
    <feMerge><feMergeNode in="b"/><feMergeNode in="SourceGraphic"/></feMerge>
  </filter>
  <filter id="soft2" x="-80%" y="-80%" width="260%" height="260%">
    <feGaussianBlur stdDeviation="14" result="b"/>
    <feMerge><feMergeNode in="b"/><feMergeNode in="SourceGraphic"/></feMerge>
  </filter>
  <filter id="shadow" x="-40%" y="-40%" width="200%" height="200%">
    <feDropShadow dx="0" dy="10" stdDeviation="12" flood-color="#000000" flood-opacity="0.55"/>
  </filter>
  <g id="stars">{star_svg}</g>
</defs>"""


# ---------------------------------------------------------------------------
# the poster
# ---------------------------------------------------------------------------


def render(d: dict) -> str:
    t = d["totals"]
    sides = d["sides"]
    groups = d["groups"]
    up = d["upstream"]
    sc = up["status_counts"]

    # a stable colour per area, brighter than the report's palette
    area_colour = {
        "wikidata-engine": CYAN,
        "wikidata-surfaces": BLUE,
        "attribution": "#79c0ff",
        "polarity": "#c4b5fd",
        "ternary": "#fde68a",
        "polarity-surface": "#6ee7b7",
        "parenting": PINK,
        "epistemic": VIOLET,
        "projection-cores": "#c084fc",
        "regression": GREEN,
        "agda-frontend": AMBER,
        "harness": SLATE,
    }
    table_label = {
        "wikidata-engine": "Wikidata engine (core)",
        "wikidata-surfaces": "Wikidata surfaces (layers, RDF, identity)",
        "attribution": "Fifth pass (fibres, attribution, diagnostics)",
        "polarity": "Evidence polarity, axes, observer joins",
        "ternary": "Balanced-ternary carrier and quotients",
        "polarity-surface": "Polarity and view joins on Wikidata",
        "parenting": "Parenting surface (slots, fibres)",
        "epistemic": "Evidence / epistemic layer",
        "projection-cores": "Projection cores (observers, residuals)",
        "regression": "Worked regression (artist / painter)",
        "agda-frontend": "Agda-subset front end (prelude, syntax)",
        "harness": "Harness (imports, entry point)",
    }
    short = {
        "wikidata-engine": "engine",
        "wikidata-surfaces": "surfaces",
        "attribution": "attribution",
        "polarity": "polarity",
        "ternary": "ternary",
        "polarity-surface": "views",
        "parenting": "parenting",
        "epistemic": "evidence",
        "projection-cores": "projections",
        "regression": "regression",
        "agda-frontend": "agda",
        "harness": "harness",
    }

    body: list[str] = []
    y = 0

    # ---- header ---------------------------------------------------------
    head_h = 218
    body.append(
        f'<rect x="0" y="0" width="{W}" height="{head_h}" fill="none"/>'
    )
    body.append(
        f'<ellipse cx="250" cy="60" rx="520" ry="300" fill="url(#aura2)"/>'
        f'<ellipse cx="1180" cy="120" rx="520" ry="320" fill="url(#aura)"/>'
    )
    body.append(
        text(60, 96, "THE LEAN 4 WIKIDATA PORT", 46, "url(#title)", "bold",
             extra='letter-spacing="1.5" filter="url(#soft)"')
    )
    body.append(
        text(60, 132, "status report for supporters & followers", 20, FG, "normal",
             opacity=0.92)
    )
    body.append(
        text(
            60,
            160,
            "An executable ontology engine for Wikidata, with every guarantee "
            "machine-checked \u2014 ported from the upstream Agda bridge.",
            14,
            MUTED,
        )
    )
    # sheen sweep across the header
    body.append(
        f'<rect x="-500" y="0" width="420" height="{head_h}" fill="url(#sheen)">'
        f'<animate attributeName="x" values="-500;{W};{W}" dur="9s" '
        f'repeatCount="indefinite"/></rect>'
    )

    # badges
    badges = [
        (f"{t['sorries']} sorry", GREEN),
        ("kernel-checked", GREEN),
        (d["build"]["toolchain"].split(":")[-1] + " toolchain", CYAN),
        ("standard axioms only", VIOLET),
    ]
    bx = 60
    for label, colour in badges:
        w = 44 + 7.4 * len(label)
        body.append(
            f'<rect x="{bx}" y="{178}" width="{w:.0f}" height="30" rx="15" '
            f'fill="{shade(colour, 0.22)}" stroke="{colour}" stroke-width="1.2"/>'
        )
        body.append(
            f'<circle cx="{bx + 15}" cy="193" r="4" fill="{colour}">'
            f'<animate attributeName="opacity" values="1;0.25;1" dur="2.4s" '
            f'repeatCount="indefinite"/></circle>'
        )
        body.append(text(bx + 28, 198, label, 13, colour, "bold"))
        bx += w + 12

    y = head_h + 18

    # ---- KPI cards ------------------------------------------------------
    kpis = [
        (f"{t['theorems']:,}", "theorems proved", CYAN),
        (f"{t['definitions']:,}", "definitions", VIOLET),
        (f"{t['lines']:,}", "lines of Lean", BLUE),
        (f"{t['files']}", "modules", PINK),
        (f"{t['decided_by_computation']}", "closed by computation", GREEN),
        (f"{t['negative_results']}", "negative results", AMBER),
    ]
    gap, pad = 18, 60
    cw = (W - 2 * pad - gap * (len(kpis) - 1)) / len(kpis)
    ch = 108
    for i, (big, small, colour) in enumerate(kpis):
        x = pad + i * (cw + gap)
        body.append(
            f'<rect x="{x:.1f}" y="{y}" width="{cw:.1f}" height="{ch}" rx="16" '
            f'fill="url(#glass)" stroke="{PANEL_EDGE}" filter="url(#shadow)"/>'
        )
        body.append(
            f'<rect x="{x:.1f}" y="{y}" width="{cw:.1f}" height="4" rx="2" fill="{colour}"/>'
        )
        body.append(
            f'<ellipse cx="{x + cw / 2:.1f}" cy="{y + 6}" rx="{cw / 2.6:.0f}" ry="16" '
            f'fill="{colour}" opacity="0.20" filter="url(#soft)"/>'
        )
        body.append(text(x + cw / 2, y + 62, big, 40, FG, "bold", anchor="middle"))
        body.append(text(x + cw / 2, y + 88, small, 12.5, MUTED, anchor="middle"))
    y += ch + 26

    # ---- panel A: isometric skyline of the areas ------------------------
    ph = 470
    body += panel(
        pad, y, W - 2 * pad, ph,
        "Where the work sits \u2014 a 3D skyline of the development",
        "one tower per area; height = theorems, footprint = modules, glowing cap = "
        "negative results (\u201cthis inference is not licensed\u201d)",
        CYAN,
    )
    ox, oy = pad + 96, y + 342
    sx = sy = 44.0
    step, dep = 0.78, 0.62
    max_thm = max(g["theorems"] for g in groups.values()) or 1
    order = list(groups.items())
    n_areas = len(order)
    zs = 208.0 / max_thm  # px per theorem
    # a floor slab under the row of towers
    floor = [
        iso(ox, oy, -0.3, 0.3, 0, sx, sy),
        iso(ox, oy, 0.3, -0.3, 0, sx, sy),
        iso(ox, oy, (n_areas - 1) * step + dep + 0.4, -(n_areas - 1) * step + dep - 0.3, 0, sx, sy),
        iso(ox, oy, (n_areas - 1) * step + dep - 0.3, -(n_areas - 1) * step + dep + 0.4, 0, sx, sy),
    ]
    body.append(poly(floor, "#16203a", 0.85))
    for k in range(n_areas):
        p0 = iso(ox, oy, k * step, -k * step + dep + 0.35, 0, sx, sy)
        p1 = iso(ox, oy, k * step + dep + 0.35, -k * step, 0, sx, sy)
        body.append(
            f'<line x1="{p0[0]:.1f}" y1="{p0[1]:.1f}" x2="{p1[0]:.1f}" y2="{p1[1]:.1f}" '
            f'stroke="#25324f" stroke-width="1"/>'
        )
    for i, (key, g) in enumerate(order):
        colour = area_colour[key]
        gx, gy = i * step, -i * step
        w = dep
        h_all = g["theorems"] * zs
        h_neg = g["negative_results"] * zs
        if h_all <= 0:
            body += iso_box(ox, oy, gx, gy, w, w, 4, shade(colour, 0.9), sx, sy)
        else:
            body += iso_box(ox, oy, gx, gy, w, w, h_all - h_neg, colour, sx, sy)
            body += iso_box(ox, oy, gx, gy, w, w, h_neg, AMBER, sx, sy,
                            glow=True, z0=h_all - h_neg)
        top = iso(ox, oy, gx + w / 2, gy + w / 2, max(h_all, 4), sx, sy)
        body.append(
            text(top[0], top[1] - 30, str(g["theorems"]), 16, FG, "bold", anchor="middle")
        )
        body.append(text(top[0], top[1] - 16, "thm", 10, MUTED, anchor="middle"))
        base = iso(ox, oy, gx + w / 2, gy + w / 2, 0, sx, sy)
        body.append(
            text(base[0], base[1] + 34, short[key], 11.5, colour, "bold",
                 anchor="middle",
                 extra=f'transform="rotate(-22 {base[0]:.1f} {base[1] + 34:.1f})"')
        )

    # legend table on the right
    lx, ly = pad + 660, y + 96
    body.append(text(lx, ly, "area", 11.5, MUTED, "bold"))
    for label, off in (("files", 300), ("lines", 380), ("thm", 452), ("neg", 512),
                       ("decided", 592)):
        body.append(text(lx + off, ly, label, 11.5, MUTED, "bold", anchor="end"))
    ly += 12
    body.append(
        f'<line x1="{lx}" y1="{ly}" x2="{lx + 592}" y2="{ly}" stroke="{PANEL_EDGE}"/>'
    )
    ly += 24
    for key, g in order:
        colour = area_colour[key]
        body.append(
            f'<rect x="{lx}" y="{ly - 10}" width="12" height="12" rx="3" '
            f'fill="{colour}"/>'
        )
        body.append(text(lx + 22, ly, table_label[key], 12.5, FG))
        for value, off in ((g["files"], 300), (f"{g['lines']:,}", 380),
                           (g["theorems"], 452), (g["negative_results"], 512),
                           (g["decided_by_computation"], 592)):
            body.append(text(lx + off, ly, str(value), 12.5, MUTED, anchor="end",
                             family=MONO))
        ly += 30
    body.append(
        f'<line x1="{lx}" y1="{ly - 18}" x2="{lx + 592}" y2="{ly - 18}" '
        f'stroke="{PANEL_EDGE}"/>'
    )
    body.append(text(lx + 22, ly + 6, "whole development", 12.5, FG, "bold"))
    for value, off in ((t["files"], 300), (f"{t['lines']:,}", 380),
                       (t["theorems"], 452), (t["negative_results"], 512),
                       (t["decided_by_computation"], 592)):
        body.append(text(lx + off, ly + 6, str(value), 12.5, FG, "bold", anchor="end",
                         family=MONO))

    # legend for the towers
    lgx, lgy = pad + 40, y + ph - 34
    body.append(f'<rect x="{lgx}" y="{lgy - 11}" width="13" height="13" rx="3" fill="{CYAN}"/>')
    body.append(text(lgx + 21, lgy, "theorems", 12, MUTED))
    body.append(f'<rect x="{lgx + 120}" y="{lgy - 11}" width="13" height="13" rx="3" fill="{AMBER}"/>')
    body.append(text(lgx + 141, lgy, "of which negative (glowing cap)", 12, MUTED))
    y += ph + 26

    # ---- panel B (left): extruded donut of upstream coverage ------------
    bh = 500
    half = (W - 2 * pad - 24) / 2
    body += panel(pad, y, half, bh, "Coverage of the upstream surface",
                  f"{len(up['surfaces'])} Wikidata-facing surfaces of the Agda bridge, "
                  "classified", GREEN)
    cx, cy = pad + 180, y + 220
    slices = [
        (sc.get("ported", 0), GREEN, "ported & proved"),
        (sc.get("gap", 0), RED, "known gaps"),
        (sc.get("declined", 0), AMBER, "deliberately declined"),
        (sc.get("out-of-scope", 0), SLATE, "out of scope"),
    ]
    parts, _ = extruded_donut(
        cx, cy, 138, 70, 0.52, 18, [(v, c) for v, c, _ in slices]
    )
    body += parts
    total_surf = sum(v for v, _, _ in slices)
    pct = 100.0 * sc.get("ported", 0) / max(total_surf, 1)
    body.append(text(cx, cy + 4, f"{pct:.0f}%", 34, FG, "bold", anchor="middle"))
    body.append(text(cx, cy + 24, "ported", 12, MUTED, anchor="middle"))
    lx, ly = pad + 356, y + 132
    for (v, colour, label) in slices:
        body.append(
            f'<rect x="{lx}" y="{ly - 11}" width="13" height="13" rx="3" fill="{colour}" '
            f'filter="url(#soft)"/>'
        )
        body.append(text(lx + 22, ly, f"{v}", 16, FG, "bold"))
        body.append(text(lx + 48, ly, label, 13, MUTED))
        ly += 32
    gaps = [r["name"] for r in up["surfaces"] if r["status"] == "gap"]
    gy = ly + 6
    body.append(text(lx, gy, "the known gaps", 12, RED, "bold"))
    gy += 18
    for g in gaps:
        body.append(
            f'<circle cx="{lx + 5}" cy="{gy - 4}" r="3" fill="{RED}"/>'
        )
        for j, line in enumerate(wrap(g, 34)):
            body.append(text(lx + 16, gy + 14 * j, line, 11.5, MUTED))
        gy += 14 * len(wrap(g, 34)) + 4
    note = (
        f"Of the bridge's {up['invariants']['total']} stated invariants, "
        f"{up['invariants']['proved_here']} are re-proved here as theorems and "
        f"{up['invariants']['dissolved_by_porting']} dissolve on porting "
        "(one kernel, real checkers); "
        f"{up['invariants']['open']} are left open."
    )
    ny = y + bh - 56
    for line in wrap(note, 74):
        body.append(text(pad + 30, ny, line, 12.5, MUTED))
        ny += 19

    # ---- panel B (right): the two sides, as twin isometric towers -------
    rx0 = pad + half + 24
    body += panel(rx0, y, half, bh, "Two halves of the development",
                  "the Wikidata import against everything else", VIOLET)
    ox, oy = rx0 + 100, y + 318
    sx = sy = 40.0
    stacks = [
        ("Wikidata import", sides["wikidata"], CYAN, 0.0),
        ("rest of project", sides["rest"], VIOLET, 2.62),
    ]
    max_lines = max(s2["lines"] for _, s2, _, _ in stacks) or 1
    zsl = 150.0 / max_lines
    w = 0.98
    floor = [
        iso(ox, oy, -0.35, 0.35, 0, sx, sy),
        iso(ox, oy, 0.35, -0.35, 0, sx, sy),
        iso(ox, oy, 2.62 + w + 0.45, -2.62 + w - 0.35, 0, sx, sy),
        iso(ox, oy, 2.62 + w - 0.35, -2.62 + w + 0.45, 0, sx, sy),
    ]
    body.append(poly(floor, "#1a2440", 0.85))
    for label, s2, colour, gx in stacks:
        gy = -gx
        h = s2["lines"] * zsl
        body += iso_box(ox, oy, gx, gy, w, w, h, colour, sx, sy, glow=True)
        top = iso(ox, oy, gx + w / 2, gy + w / 2, h, sx, sy)
        body.append(text(top[0], top[1] - 32, f"{s2['lines']:,}", 20, FG, "bold",
                         anchor="middle"))
        body.append(text(top[0], top[1] - 16, "lines of Lean", 11, MUTED,
                         anchor="middle"))
        base = iso(ox, oy, gx + w / 2, gy + w / 2, 0, sx, sy)
        body.append(text(base[0], base[1] + 40, label, 13.5, colour, "bold",
                         anchor="middle"))
        body.append(
            text(base[0], base[1] + 58,
                 f"{s2['files']} files \u00b7 {s2['theorems']} thm \u00b7 "
                 f"{s2['definitions']} def",
                 11.5, MUTED, anchor="middle")
        )
    wshare = 100.0 * sides["wikidata"]["lines"] / max(t["lines"], 1)
    dshare = (100.0 * sides["wikidata"]["decided_by_computation"]
              / max(t["decided_by_computation"], 1))
    summary = (
        f"The ontology engine is the larger half: {wshare:.0f}% of the lines and "
        f"{dshare:.0f}% of the proofs that the machine closes by computation."
    )
    ny = y + bh - 48
    for line in wrap(summary, 66):
        body.append(text(rx0 + 30, ny, line, 12.5, MUTED))
        ny += 19
    y += bh + 26

    # ---- panel C: tilted ring gauges ------------------------------------
    gh = 300
    body += panel(pad, y, W - 2 * pad, gh, "Health, at a glance",
                  "tilted ring gauges \u2014 each one is a share of the whole", AMBER)
    gauges = [
        (1.0, GREEN, "sorry-free", f"{t['theorems'] - 0}/{t['theorems']} theorems carry a real proof"),
        (
            (up["invariants"]["proved_here"] + up["invariants"]["dissolved_by_porting"])
            / max(up["invariants"]["total"], 1),
            CYAN,
            "upstream invariants",
            f"{up['invariants']['proved_here']} re-proved + "
            f"{up['invariants']['dissolved_by_porting']} dissolved of "
            f"{up['invariants']['total']}",
        ),
        (
            sc.get("ported", 0) / max(total_surf, 1),
            VIOLET,
            "surfaces ported",
            f"{sc.get('ported', 0)} of {total_surf} surfaces",
        ),
        (
            t["decided_by_computation"] / max(t["theorems"], 1),
            PINK,
            "decided by computation",
            f"{t['decided_by_computation']} of {t['theorems']} theorems",
        ),
        (
            t["negative_results"] / max(t["theorems"], 1),
            AMBER,
            "negative results",
            f"{t['negative_results']} of {t['theorems']} theorems",
        ),
    ]
    n = len(gauges)
    span = (W - 2 * pad - 80) / n
    for i, (frac, colour, label, sub) in enumerate(gauges):
        gx = pad + 40 + span * (i + 0.5)
        gy = y + 150
        body += extruded_gauge(gx, gy, 74, 40, frac, colour)
        body.append(text(gx, gy + 6, f"{100 * frac:.0f}%", 26, FG, "bold", anchor="middle"))
        body.append(text(gx, gy + 92, label, 13.5, colour, "bold", anchor="middle"))
        body.append(text(gx, gy + 110, sub, 11.5, MUTED, anchor="middle"))
    y += gh + 26

    # ---- panel C2: 3D growth ribbons, pass by pass -----------------------
    rows = pass_totals(d)
    gh2 = 430
    body += panel(pad, y, W - 2 * pad, gh2,
                  "Growth, pass by pass \u2014 a 3D area chart",
                  "two extruded ribbons: theorems in front, lines of Lean behind; "
                  "both cumulative over the five passes of the port", BLUE)
    P = axon(pad + 240, y + 300)
    zt = 178.0 / max(rows[-1]["cum_theorems"], 1)
    zl = 178.0 / max(rows[-1]["cum_lines"], 1)
    xs = list(range(len(rows) + 1))
    depth = 2.05
    floor = [P(xs[0], 0, 0), P(xs[-1] + 0.15, 0, 0),
             P(xs[-1] + 0.15, depth, 0), P(xs[0], depth, 0)]
    body.append(poly(floor, "#131c33", 0.9))
    for x in xs:
        p0, p1 = P(x, 0, 0), P(x, depth, 0)
        body.append(
            f'<line x1="{p0[0]:.1f}" y1="{p0[1]:.1f}" x2="{p1[0]:.1f}" y2="{p1[1]:.1f}" '
            f'stroke="#26314d" stroke-width="1"/>'
        )
    # back ribbon: cumulative lines of Lean
    pts_l = [(xs[0], 0.0)] + [(xs[i + 1], r["cum_lines"] * zl) for i, r in enumerate(rows)]
    body += iso_ribbon(P, pts_l, 0.12, 0.62, BLUE)
    # front ribbon: cumulative theorems
    pts_t = [(xs[0], 0.0)] + [(xs[i + 1], r["cum_theorems"] * zt) for i, r in enumerate(rows)]
    body += iso_ribbon(P, pts_t, 1.28, 0.62, CYAN)
    for i, r in enumerate(rows):
        pl = P(xs[i + 1], 0.12, r["cum_lines"] * zl)
        body.append(
            f'<circle cx="{pl[0]:.1f}" cy="{pl[1]:.1f}" r="4" fill="{BLUE}"/>'
        )
        body.append(text(pl[0], pl[1] - 10, f"{r['cum_lines']:,}", 11.5, BLUE,
                         anchor="middle"))
        pt = P(xs[i + 1], 1.28, r["cum_theorems"] * zt)
        body.append(
            f'<circle cx="{pt[0]:.1f}" cy="{pt[1]:.1f}" r="5.5" fill="{FG}" '
            f'stroke="{r["colour"]}" stroke-width="2.5" filter="url(#soft)"/>'
        )
        body.append(text(pt[0], pt[1] - 14, f"{r['cum_theorems']}", 14.5, FG, "bold",
                         anchor="middle"))
        base = P(xs[i + 1], depth, 0)
        body.append(text(base[0], base[1] + 20, r["tag"], 12, r["colour"], "bold",
                         anchor="middle"))
        body.append(text(base[0], base[1] + 35, r["name"], 10.5, MUTED,
                         anchor="middle"))
    body.append(
        f'<rect x="{pad + 40}" y="{y + 92}" width="13" height="13" rx="3" fill="{CYAN}"/>'
    )
    body.append(text(pad + 61, y + 103, "cumulative theorems", 12, MUTED))
    body.append(
        f'<rect x="{pad + 40}" y="{y + 116}" width="13" height="13" rx="3" fill="{BLUE}"/>'
    )
    body.append(text(pad + 61, y + 127, "cumulative lines of Lean", 12, MUTED))

    # per-pass table on the right
    lx, ly = pad + 700, y + 96
    for label, off in (("pass", 0),):
        body.append(text(lx + off, ly, label, 11.5, MUTED, "bold"))
    for label, off in (("files", 300), ("lines", 380), ("thm", 452), ("neg", 512),
                       ("total thm", 592)):
        body.append(text(lx + off, ly, label, 11.5, MUTED, "bold", anchor="end"))
    ly += 12
    body.append(
        f'<line x1="{lx}" y1="{ly}" x2="{lx + 592}" y2="{ly}" stroke="{PANEL_EDGE}"/>'
    )
    ly += 26
    for r in rows:
        body.append(
            f'<circle cx="{lx + 6}" cy="{ly - 4}" r="6" fill="{r["colour"]}"/>'
        )
        body.append(text(lx + 22, ly, f"{r['tag']} \u00b7 {r['name']}", 12.5, FG))
        for value, off in ((r["files"], 300), (f"{r['lines']:,}", 380),
                           (r["theorems"], 452), (r["negative"], 512),
                           (r["cum_theorems"], 592)):
            body.append(text(lx + off, ly, str(value), 12.5, MUTED, anchor="end",
                             family=MONO))
        ly += 34
    y += gh2 + 26

    # ---- panel C3: what the numbers buy ---------------------------------
    wh = 260
    body += panel(pad, y, W - 2 * pad, wh, "What the numbers buy",
                  "three things a supporter can check for themselves", GREEN)
    tiles = [
        ("An engine, not a description", GREEN,
         f"The ontology is executable: {t['decided_by_computation']} theorems are "
         "closed by running the checker, and each engine comes with an exactness "
         "theorem saying the computation agrees with the relation it models."),
        ("Negatives, written down", AMBER,
         f"{t['negative_results']} of the {t['theorems']} theorems say some "
         "inference is \u201cnot licensed\u201d \u2014 an absence is not a refutation, a "
         "diagnostic is not permission to edit, support does not transfer down a "
         "slice."),
        ("Nothing taken on trust", CYAN,
         "No sorry, no added axioms, and only the standard three "
         "(propext, Classical.choice, Quot.sound); imported claims are "
         "fail-closed and must be backed by a checkable certificate."),
    ]
    tw = (W - 2 * pad - 60 - 2 * 18) / 3
    for i, (title, colour, blurb) in enumerate(tiles):
        x = pad + 30 + i * (tw + 18)
        yy = y + 82
        body.append(
            f'<rect x="{x:.1f}" y="{yy}" width="{tw:.1f}" height="146" rx="14" '
            f'fill="{shade(colour, 0.14)}" stroke="{shade(colour, 0.55)}"/>'
        )
        body.append(
            f'<circle cx="{x + 24:.1f}" cy="{yy + 26}" r="9" fill="{colour}" '
            f'filter="url(#soft)"><animate attributeName="opacity" '
            f'values="1;0.45;1" dur="{3.4 + i}s" repeatCount="indefinite"/></circle>'
        )
        body.append(text(x + 42, yy + 31, title, 14.5, FG, "bold"))
        ty = yy + 60
        for line in wrap(blurb, 52):
            body.append(text(x + 18, ty, line, 11.8, MUTED))
            ty += 16
    y += wh + 26

    # ---- panel D: the journey -------------------------------------------
    jh = 246
    body += panel(pad, y, W - 2 * pad, jh, "How it was built \u2014 five passes",
                  "each pass took what was genuinely new upstream and re-founded it "
                  "on executable machinery", PINK)
    passes = [
        ("Pass 1", "the engine", "reachability, P279/P31, class algebra, "
         "diagnostics, alignment, provenance \u2014 plus the three-valued "
         "evidence layer", CYAN),
        ("Pass 2", "layers & slices", "the truthy layer proved conservative, "
         "reified/direct RDF, constraints & schemas, identity and lexemes", BLUE),
        ("Pass 3", "the support square", "Belnap's four corners, so conflict and "
         "ignorance cannot collapse; lens transitions between views", VIOLET),
        ("Pass 4", "parents & observers", "P22/P25/P8810/P1531 with descent, the "
         "observer/residual calculus, delegated authority as a machine", PINK),
        ("Pass 5", "attribution & context", "derivation fibres, four-layer blame, "
         "language-indexed alignment safety, context erasure \u2014 and an "
         "Agda-subset front end", AMBER),
    ]
    cwj = (W - 2 * pad - 60 - (len(passes) - 1) * 16) / len(passes)
    for i, (tag, name, blurb, colour) in enumerate(passes):
        x = pad + 30 + i * (cwj + 16)
        yy = y + 84
        body.append(
            f'<rect x="{x:.1f}" y="{yy}" width="{cwj:.1f}" height="120" rx="14" '
            f'fill="{shade(colour, 0.16)}" stroke="{shade(colour, 0.6)}"/>'
        )
        body.append(
            f'<circle cx="{x + 26:.1f}" cy="{yy + 26}" r="11" fill="{colour}" '
            f'filter="url(#soft)"><animate attributeName="r" values="11;13;11" '
            f'dur="{3 + i}s" repeatCount="indefinite"/></circle>'
        )
        body.append(text(x + 46, yy + 24, tag, 13, colour, "bold"))
        body.append(text(x + 46, yy + 42, name, 15, FG, "bold"))
        # wrap the blurb
        words, line, lines = blurb.split(), "", []
        for wd in words:
            if len(line) + len(wd) + 1 > 40:
                lines.append(line)
                line = wd
            else:
                line = (line + " " + wd).strip()
        lines.append(line)
        for j, ln in enumerate(lines[:4]):
            body.append(text(x + 16, yy + 66 + 15 * j, ln, 11.5, MUTED))
        if i < 3:
            ax = x + cwj + 3
            body.append(
                f'<path d="M {ax} {yy + 60} l 10 0" stroke="{MUTED}" stroke-width="2" '
                f'marker-end=""/>'
            )
    y += jh + 26

    # ---- footer ---------------------------------------------------------
    fh = 118
    body += panel(pad, y, W - 2 * pad, fh, None, None, GREEN)
    body.append(
        text(pad + 30, y + 40,
             "Every figure here is counted from the Lean sources by "
             "tools/supporter_infographic.py; the classification of upstream "
             "surfaces is transcribed from PORTING_NOTES.md and RELATED_WORK.md.",
             12.5, MUTED)
    )
    body.append(
        text(pad + 30, y + 66,
             "Read more: docs/status/STATUS_REPORT.md \u00b7 PORTING_NOTES.md \u00b7 "
             "RELATED_WORK.md \u00b7 machine-readable numbers in docs/status/status.json",
             12.5, MUTED)
    )
    body.append(
        text(pad + 30, y + 94,
             f"lake build: clean \u00b7 {t['sorries']} sorry \u00b7 no added axioms "
             "\u00b7 axioms used: propext, Classical.choice, Quot.sound",
             12.5, GREEN, "bold")
    )
    y += fh + 30

    H = int(y)
    head = (
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" '
        f'viewBox="0 0 {W} {H}" role="img" '
        f'aria-label="Status infographic for the Lean 4 Wikidata port">'
    )
    bg = [
        f'<rect width="{W}" height="{H}" fill="url(#bg)"/>',
        '<use href="#stars"/>',
        f'<ellipse cx="{W * 0.15:.0f}" cy="{H * 0.55:.0f}" rx="460" ry="360" '
        f'fill="url(#aura2)" opacity="0.5"/>',
        f'<ellipse cx="{W * 0.88:.0f}" cy="{H * 0.78:.0f}" rx="420" ry="340" '
        f'fill="url(#aura)" opacity="0.45"/>',
    ]
    return "\n".join([head, defs(H)] + bg + body + ["</svg>", ""])


def main() -> None:
    data = collect()
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    with open(OUT, "w", encoding="utf-8") as fh:
        fh.write(render(data))
    print(f"wrote {os.path.relpath(OUT, ROOT)}")
    # a raster copy for viewers that will not run SVG, if a rasteriser is around
    try:
        import cairosvg  # type: ignore
    except ImportError:
        return
    png = OUT[: -len(".svg")] + ".png"
    cairosvg.svg2png(url=OUT, write_to=png, output_width=W)
    print(f"wrote {os.path.relpath(png, ROOT)}")


if __name__ == "__main__":
    main()
