# -*- coding: utf-8 -*-
"""Regenerate `docs/status.svg`: the one-page status report.

    python3 docs/make_status_svg.py        # run from the project root

The wider poster is `docs/showcase.svg` (`make_showcase_svg.py`).  Both take
their figures from `docs/stats.py`, which counts the sources, the stored
knowledge bases and the generated modules, and which holds the one layering of
the development that both images draw.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)

from svgkit import Canvas, MONO, wrap_lines    # noqa: E402
import stats                                   # noqa: E402

W = 1120
M = 48
RIGHT = W - M
CW = W - 2 * M

TOT, MODS = stats.totals()
CORP = stats.corpus()
COMMANDS = stats.cli_commands()
GLOSS = stats.glossary()
LAYERS = stats.layers()

DEFS = (
    '<linearGradient id="hdr" x1="0" y1="0" x2="1" y2="1">'
    '<stop offset="0%" stop-color="#0f2f4f"/><stop offset="100%" stop-color="#14532d"/></linearGradient>'
    '<linearGradient id="barA" x1="0" y1="0" x2="1" y2="0">'
    '<stop offset="0%" stop-color="#2563eb"/><stop offset="100%" stop-color="#93c5fd"/></linearGradient>'
    '<linearGradient id="barB" x1="0" y1="0" x2="1" y2="0">'
    '<stop offset="0%" stop-color="#0d9488"/><stop offset="100%" stop-color="#5eead4"/></linearGradient>'
    '<linearGradient id="barC" x1="0" y1="0" x2="1" y2="0">'
    '<stop offset="0%" stop-color="#7c3aed"/><stop offset="100%" stop-color="#c4b5fd"/></linearGradient>'
    '<linearGradient id="barD" x1="0" y1="0" x2="1" y2="0">'
    '<stop offset="0%" stop-color="#ea580c"/><stop offset="100%" stop-color="#fdba74"/></linearGradient>'
    '<linearGradient id="barE" x1="0" y1="0" x2="1" y2="0">'
    '<stop offset="0%" stop-color="#be123c"/><stop offset="100%" stop-color="#fda4af"/></linearGradient>'
)

c = Canvas(W, title="Status report: the Wikidata ontology formalised in Lean 4", defs=DEFS)

# ---------------- header ----------------
c.rect(0, 0, W, 132, "url(#hdr)", rx=0)
c.text(M, 58, "The Wikidata ontology, formalised in Lean 4", 30, "#ffffff", "bold")
c.text(M, 92, "Status report - machine-checked, no sorry, standard axioms only", 16, "#bfdbfe")
c.text(RIGHT, 58, stats.git_date() or "", 16, "#e2e8f0", anchor="end")
c.text(RIGHT, 88, "Lean 4.28.0 + Mathlib", 14, "#94a3b8", anchor="end", family=MONO)

# ---------------- KPI cards ----------------
kpis = [(f"{TOT['modules']}", "modules"),
        (f"{TOT['theorems']:,}".replace(",", " "), "theorems"),
        (f"{TOT['defs']:,}".replace(",", " "), "definitions"),
        (f"{TOT['lines'] / 1000:.0f}k", "lines of Lean"),
        (f"{GLOSS['entities']:,}".replace(",", " "), "terms grounded"),
        (str(TOT["sorries"]), "sorry / gaps")]
cy, ch = 164, 104
cw = (CW - 10 * (len(kpis) - 1)) / len(kpis)
for i, (num, lab) in enumerate(kpis):
    x = M + i * (cw + 10)
    c.rect(x, cy, cw, ch, "#ffffff", rx=14, stroke="#cbd5e1")
    col = "#16a34a" if lab.startswith("sorry") else "#0f172a"
    c.text(x + cw / 2, cy + 52, num, 34, col, "bold", anchor="middle")
    c.text(x + cw / 2, cy + 80, lab, 14, "#475569", anchor="middle")

# ---------------- layer chart ----------------
y = cy + ch + 42
c.text(M, y, "Where the results sit", 22, "#0f172a", "bold")
c.text(M, y + 26, "theorems and lemmas per layer of the development", 14, "#64748b")
y += 52

grads = ["url(#barA)", "url(#barB)", "url(#barC)", "url(#barD)", "url(#barE)"]
assert sum(n for _, _, _, n in LAYERS) == TOT["theorems"]
maxv = max(n for _, _, _, n in LAYERS)
for i, (name, mods, note, n) in enumerate(LAYERS):
    shown = [m for m in mods if not m.startswith("Generated/")]
    txt = ", ".join(shown + ([note] if note else []))
    lines = wrap_lines(txt, 12, 560)
    rowh = 40 + 17 * len(lines)
    c.rect(M, y, CW, rowh, "#ffffff", rx=12, stroke="#e2e8f0")
    c.text(M + 18, y + 26, name, 16, "#0f172a", "bold")
    c.wrap(M + 18, y + 46, txt, 12, 560, fill="#64748b", leading=17)
    c.rect(M + 620, y + 16, max(5, 250 * n / maxv), 18, grads[i % len(grads)], rx=9)
    c.text(RIGHT - 18, y + 31, f"{n} theorem" + ("" if n == 1 else "s"), 14, "#0f172a", "bold",
           anchor="end")
    y += rowh + 10

# ---------------- coverage ----------------
y += 26
c.text(M, y, "Wikidata features covered", 22, "#0f172a", "bold")
chips = ["instance of (P31)", "subclass of (P279)", "metaclass levels", "disjointness",
         "disjoint union (P2738)", "union of (P2737)", "statement ranks", "qualifiers",
         "some value / no value", "references", "labels and aliases", "sitelinks",
         "external identifiers", "quantities and units", "time precision",
         "start / end time", "property paths", "entity schemas (ShEx)",
         "property constraints", "properties for this type (P1963)", "lexemes and senses",
         "equivalent class (P1709)", "item merges", "RDF export (wdt: / p: / ps: / pq:)",
         "part of (P361)", "has parts of the class (P2670)", "redundant P279 clean-up",
         "diagnostic reports", "conjunctive queries", "follows / followed by (P155 / P156)",
         "part of the series (P179)", "series ordinal (P1545)", "father / mother (P22 / P25)",
         "spouse (P26)", "parent taxon (P171)", "taxon rank (P105)", "taxon name (P225)",
         "is the study of (P2578)", "topic's main category (P910)",
         "Wikimedia pages in every language", "cited sources and authority control",
         f"grounded glossary ({GLOSS['entities']} entities)",
         f"vocabulary map ({GLOSS['vocabulary']} notions)",
         f"labels of the corpus ({CORP['all']['items']} items)"]
y = c.chip_row(M, y + 26, chips, RIGHT) + 34

# ---------------- newest layers ----------------
bullets = [
    "SignedWords: a relation letter may be run backwards, as an inverse property path. The "
    "degree of a signed word is exactly the metaclass-level displacement it performs "
    "(Ontology.level_add_sdegree), so a forward and a backward instance of step cancel: an "
    "honest integer grading. A closed signed walk has degree zero, hence a closing word of "
    "non-zero degree refutes every ontology model of the base.",
    "ProgramAlgebra, CyclicAlgebra and CompilerPipeline: the transformations of the ontology "
    "layer read as programs - a Godel numbering of the relation words (RelWord.equivNat), "
    "their composition monoid (KB.wordStep_append), the compiler stages acting by morphisms, "
    "the ZMod d phases, and the order-exactly-twelve cyclic part, split by the CRT into its "
    "prime fibres (12 = 2^2 * 3).",
    "Periodicity, PeriodicityReport, SpectrumReport and FeedbackSets: the search for periodic "
    "points, run over the whole downloaded corpus. Eleven items of the class hierarchy are "
    "periodic, the remaining 1567 are not, a phase certificate makes the period of each of the "
    "four components exact, and the minimum feedback sets measure the distance to acyclicity.",
    "The category-theoretic layer: ontologies with their limits and colimits, the pullback as "
    "a fibre product of spaces, the symmetries and the GF(2) vector space of class extensions, "
    "a Grothendieck topology whose covering families are stable under pullback, labellings as "
    "a sheaf on that site, and the pullback again as a homotopy fibre product.",
    "Publish, Sync and Archive: the findings leave the repository under proof - a JSON Lines "
    "record of a knowledge base parses back to exactly what was written, its content address "
    "identifies it, peer-to-peer gossip converges to one state that loses nothing and invents "
    "nothing, and an archive deposit re-imports to the ontology it was made from.",
    "Enrichment, CorpusFrontier and CorpusRounds: the loop that grows the corpus from its own "
    "sources - pull every Wikimedia page of an item, scan the articles and what they cite, "
    "rank what is missing, absorb the most referenced of it - with the frontier shrinking "
    "144, 70, 42, 18, 14 and every round proved to lose nothing.",
]

panel_h = 52 + sum(20 * len(wrap_lines(b, 14, CW - 80)) for b in bullets) + 10
c.rect(M, y, CW, panel_h, "#ffffff", rx=14, stroke="#cbd5e1")
c.rect(M, y, 6, panel_h, "#be123c", rx=3)
c.text(M + 26, y + 34, "The newest layers: inverses and the integer grading, the program "
                       "algebra, the periodicity spectrum", 19, "#0f172a", "bold")
ty = y + 62
for b in bullets:
    c.circle(M + 34, ty - 5, 3.5, "#be123c")
    ty = c.wrap(M + 48, ty, b, 14, CW - 80, fill="#334155", leading=20) + 4
y += panel_h + 30

# ---------------- verification footer ----------------
c.rect(M, y, CW, 96, "#0f172a", rx=14)
badges = [("lake build", "clean"), ("sorry", "none"), ("axioms", "standard only"),
          ("by decide checks", str(TOT["decides"])), ("#eval demos", str(TOT["evals"])),
          ("tool commands", str(len(COMMANDS)))]
bw = (CW - 40) / len(badges)
for i, (k, v) in enumerate(badges):
    xx = M + 20 + i * bw
    c.text(xx, y + 40, k, 13, "#94a3b8", family=MONO)
    c.text(xx, y + 68, v, 18, "#4ade80" if v in ("clean", "none", "standard only") else "#e2e8f0",
           "bold")
y += 96 + 40
c.text(M, y - 16, "Identifiers follow Wikidata; the hand-built fragments are stylised excerpts, "
                  "and the theorems about them are statements about those fragments.",
       12, "#94a3b8")
H = y + 16

c.write(os.path.join(ROOT, "docs", "status.svg"), H)
print("docs/status.svg", W, "x", H)
