# -*- coding: utf-8 -*-
"""Regenerate `docs/showcase.svg`: the ontology-and-tools showcase poster.

    python3 docs/make_showcase_svg.py      # run from the project root

Every figure comes from `docs/stats.py`, which counts the sources, the stored
knowledge bases and the generated modules, so the poster cannot drift away from
the repository.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, HERE)

from svgkit import Canvas, FONT, MONO, width_of, wrap_lines   # noqa: E402
import stats                                      # noqa: E402

W = 1280
M = 48                       # page margin
RIGHT = W - M
CW = W - 2 * M               # content width

TOT, MODS = stats.totals()
CORP = stats.corpus()
DERIVED = CORP["_derived"]
COMMANDS = stats.cli_commands()
GLOSS = stats.glossary()
GAIN = stats.merge_gain()
LAYERS = stats.layers()

DEFS = (
    '<linearGradient id="hdr" x1="0" y1="0" x2="1" y2="1">'
    '<stop offset="0%" stop-color="#0b2545"/><stop offset="55%" stop-color="#12395c"/>'
    '<stop offset="100%" stop-color="#134e35"/></linearGradient>'
    '<linearGradient id="g1" x1="0" y1="0" x2="1" y2="0">'
    '<stop offset="0%" stop-color="#2563eb"/><stop offset="100%" stop-color="#93c5fd"/></linearGradient>'
    '<linearGradient id="g2" x1="0" y1="0" x2="1" y2="0">'
    '<stop offset="0%" stop-color="#0d9488"/><stop offset="100%" stop-color="#5eead4"/></linearGradient>'
    '<linearGradient id="g3" x1="0" y1="0" x2="1" y2="0">'
    '<stop offset="0%" stop-color="#7c3aed"/><stop offset="100%" stop-color="#c4b5fd"/></linearGradient>'
    '<linearGradient id="g4" x1="0" y1="0" x2="1" y2="0">'
    '<stop offset="0%" stop-color="#ea580c"/><stop offset="100%" stop-color="#fdba74"/></linearGradient>'
    '<linearGradient id="g5" x1="0" y1="0" x2="1" y2="0">'
    '<stop offset="0%" stop-color="#be123c"/><stop offset="100%" stop-color="#fda4af"/></linearGradient>'
    '<marker id="arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" '
    'orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="#64748b"/></marker>'
    '<marker id="arrowW" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" '
    'orient="auto-start-reverse"><path d="M 0 0 L 10 5 L 0 10 z" fill="#e2e8f0"/></marker>'
)

c = Canvas(W, background="#f1f5f9",
           title="Showcase: the Wikidata ontology formalised in Lean 4, and the tools built on it",
           defs=DEFS)


def section(y, title, subtitle=None):
    c.text(M, y, title, 23, "#0f172a", "bold")
    if subtitle:
        c.text(M, y + 24, subtitle, 14, "#64748b")
        return y + 46
    return y + 24


# ============================== header ======================================
c.rect(0, 0, W, 148, "url(#hdr)", rx=0)
c.text(M, 60, "The Wikidata ontology, formalised in Lean 4", 32, "#ffffff", "bold")
c.text(M, 94, "A showcase of the ontology layers, what is proved about them, and the tools that "
              "run on real Wikidata data", 16, "#bfdbfe")
c.text(M, 122, "Wikidata:WikiProject Ontology  ·  machine-checked, no sorry, standard axioms only",
       13, "#93c5fd", family=MONO)
c.text(RIGHT, 60, stats.git_date() or "", 15, "#e2e8f0", anchor="end")
c.text(RIGHT, 88, "Lean 4.28.0 + Mathlib", 13, "#94a3b8", anchor="end", family=MONO)
c.text(RIGHT, 112, f"{TOT['modules']} modules · {TOT['theorems']} theorems", 13, "#94a3b8",
       anchor="end", family=MONO)

# ============================== KPI strip ===================================
kpis = [(f"{TOT['theorems']:,}".replace(",", " "), "theorems and lemmas"),
        (f"{TOT['defs']:,}".replace(",", " "), "definitions"),
        (f"{TOT['lines'] / 1000:.1f}k", "lines of Lean"),
        (f"{len(COMMANDS)}", "tool commands"),
        (f"{CORP['all']['items']}", "Wikidata items downloaded"),
        (f"{GLOSS['entities']}", "terms grounded in Wikidata"),
        (str(TOT["sorries"]), "sorry / gaps")]
cy, ch = 176, 100
cwid = (CW - 10 * (len(kpis) - 1)) / len(kpis)
for i, (num, lab) in enumerate(kpis):
    x = M + i * (cwid + 10)
    c.rect(x, cy, cwid, ch, "#ffffff", rx=14, stroke="#cbd5e1")
    col = "#16a34a" if lab.startswith("sorry") else "#0f172a"
    c.text(x + cwid / 2, cy + 50, num, 32, col, "bold", anchor="middle")
    c.wrap(x + 14, cy + 74, lab, 13, cwid - 28, fill="#475569")
y = cy + ch + 38

# ====================== 1. the five hierarchies =============================
y = section(y, "The ontology: five hierarchies, kept apart",
            "each one a computable layer over the knowledge base, with an engine proved to "
            "decide exactly the closure of the asserted statements")

cards = [
    ("Taxonomy", "url(#g1)", "#1d4ed8",
     "instance of P31 · subclass of P279",
     ["derived subclass of = reflexive-transitive closure of the statements",
      "the class hierarchy is a partial order; instances inherit upwards",
      "instance of is not transitive - a decided counterexample",
      "metaclass levels drop by one across P31, are constant across P279"],
     ["Core", "Engine", "Reachability", "Subsumption", "Taxonomy"]),
    ("Meronomy", "url(#g2)", "#0f766e",
     "part of P361 · has parts of the class P2670",
     ["part-of is a partial order and well founded, so induction upwards is legitimate",
      "the meronomy is atomistic: every item has a part with no proper parts",
      "P2670 expectations are inherited down subclass of",
      "part of is not inherited through instance of; supplementation and",
      "extensionality both fail on valid fragments"],
     ["Mereology"]),
    ("Kinship", "url(#g3)", "#6d28d9",
     "father P22 · mother P25 · spouse P26",
     ["ancestry is decided, is a partial order and is well founded",
      "at most one father and one mother, so at most two parents",
      "siblinghood symmetric and irreflexive; relatedness is not transitive",
      "a validated layer never confuses parenthood with the taxonomy"],
     ["Kinship", "KinshipDiagnostics"]),
    ("Series", "url(#g4)", "#c2410c",
     "follows P155 · followed by P156 · part of the series P179 · series ordinal P1545",
     ["coming after is a partial order and well founded: every item has an origin",
      "a chain has a unique origin, and walking it out enumerates it exactly once",
      "consistent ordinals are a local check that already rules out cycles",
      "P155/P156 read as an inverse pair derive exactly the intended statements"],
     ["Series", "SeriesChain", "SeriesExamples", "SeriesDiagnostics"]),
    ("Biological taxa", "url(#g5)", "#9f1239",
     "parent taxon P171 · taxon rank P105 · taxon name P225",
     ["descent is a partial order, well founded, so every taxon has a root",
      "ranks certify acyclicity by two purely local checks",
      "one parent per taxon makes a tree with a unique root",
      "taxon name is injective; P171 is never a taxonomy statement"],
     ["Taxa", "TaxaLineage", "TaxaDiagnostics", "TaxaExamples"]),
]

col_w = (CW - 2 * 14) / 3


def card_height(props, facts, mods):
    h = 56 + 17 * len(wrap_lines(props, 12.5, col_w - 36, family=MONO)) + 6
    for f in facts:
        h += 16 * len(wrap_lines(f, 12.5, col_w - 52)) + 2
    return h + 14 * len(wrap_lines(" · ".join(mods), 10.5, col_w - 36, family=MONO)) + 16


card_h = max(card_height(p, f, m) for _, _, _, p, f, m in cards)
for i, (name, grad, colour, props, facts, mods) in enumerate(cards):
    col, row = i % 3, i // 3
    x = M + col * (col_w + 14)
    yy = y + row * (card_h + 14)
    c.rect(x, yy, col_w, card_h, "#ffffff", rx=14, stroke="#cbd5e1")
    c.rect(x, yy, col_w, 6, grad, rx=3)
    c.text(x + 18, yy + 34, name, 19, "#0f172a", "bold")
    n = sum(MODS[m]["theorems"] for m in mods)
    c.text(x + col_w - 18, yy + 34, f"{n} theorems", 13, colour, "bold", anchor="end")
    ty = c.wrap(x + 18, yy + 56, props, 12.5, col_w - 36, fill=colour, family=MONO, leading=17)
    ty += 6
    for f in facts:
        c.circle(x + 22, ty - 4, 2.5, colour)
        ty = c.wrap(x + 32, ty, f, 12.5, col_w - 52, fill="#334155", leading=16)
        ty += 2
    mlines = wrap_lines(" · ".join(mods), 10.5, col_w - 36, family=MONO)
    c.wrap(x + 18, yy + card_h - 12 - 14 * (len(mlines) - 1), " · ".join(mods), 10.5,
           col_w - 36, fill="#94a3b8", family=MONO, leading=14)

# the sixth cell: how they relate
x = M + 2 * (col_w + 14)
yy = y + card_h + 14
c.rect(x, yy, col_w, card_h, "#0f172a", rx=14)
c.text(x + 18, yy + 34, "Separation, proved", 19, "#ffffff", "bold")
c.wrap(x + 18, yy + 60,
       "Wikidata:WikiProject Ontology insists the class hierarchy is not the family tree, "
       "not the parts hierarchy, not the series and not the tree of life. Each layer carries "
       "that as a validated obligation, and each engine is proved to decide only its own "
       "relation: a P171, P361, P22 or P155 statement between items already related by P279 "
       "or P31 is a reported defect.",
       12.5, col_w - 36, fill="#cbd5e1", leading=17)
y = yy + card_h + 36

# ====================== 2. the data model ===================================
y = section(y, "The data model around the hierarchies",
            "statements are more than pairs of items: the layers below are formalised too")
chips = ["metaclass levels", "disjointness", "disjoint union P2738", "union of P2737",
         "equivalent class P1709", "statement ranks", "qualifiers", "some value / no value",
         "references and provenance", "labels, aliases, descriptions", "sitelinks",
         "external identifiers", "quantities and units", "time values and precision",
         "start time / end time", "property paths", "property constraints",
         "properties for this type P1963", "entity schemas (ShEx)", "lexemes and senses",
         "RDF export: wdt: p: ps: pq:", "item merges and redirects", "redundant P279 clean-up",
         "conjunctive queries with variables", "witnessed diagnostic reports",
         "is the study of P2578", "topic's main category P910",
         "Wikimedia pages in every language", "cited sources", "authority control",
         "labels, descriptions and aliases of the whole corpus"]
y = c.chip_row(M, y, chips, RIGHT) + 34

# ====================== 3. the toolchain ====================================
y = section(y, "The tools: a certified pipeline from the live API to a Lean module",
            "each stage is an executable command whose guarantee is a theorem of the library")

stages = [
    ("fetch / import", "wikidata fetch Q42 --depth 3",
     "downloads Special:EntityData JSON, follows P31/P279, caches it",
     "imports exactly the claims in the source, nothing invented"),
    ("check", "wikidata check f.wdkb",
     "runs the validator and prints one witnessed defect per line",
     "the report is empty exactly when the base is valid"),
    ("derive / ask / why", "wikidata why f.wdkb Q5 Q154954",
     "the entailed facts, a yes/no answer, or an explaining chain",
     "sound and conservative; the printed chain is re-checked"),
    ("query", "wikidata query f.wdkb 'inst ?x Q5'",
     "conjunctive queries with variables over derived or asserted facts",
     "the evaluator is sound and complete for the query semantics"),
    ("merge / normalize", "wikidata merge data/*.wdkb --dedup",
     "one corpus out of many downloads, repetitions dropped",
     "nothing is lost: every fact of every fragment still follows"),
    ("lean", "wikidata lean corpus.wdkb --module M",
     "compiles the base and all it entails into a Lean module",
     "Lean re-checks the facts are exactly right on every build"),
]
box_w = (CW - 5 * 16) / 6


def stage_height(cmd, what, guarantee):
    h = 62 + 14 * len(wrap_lines(cmd, 10.5, box_w - 24, family=MONO))
    h += 10 + 15 * len(wrap_lines(what, 11.5, box_w - 24))
    return h + 20 + 15 * len(wrap_lines(guarantee, 11.5, box_w - 24)) + 6


box_h = max(stage_height(cmd, what, g) for _, cmd, what, g in stages)
for i, (name, cmd, what, guarantee) in enumerate(stages):
    x = M + i * (box_w + 16)
    c.rect(x, y, box_w, box_h, "#ffffff", rx=13, stroke="#cbd5e1")
    c.rect(x, y, box_w, 40, "#0f2f4f", rx=13)
    c.rect(x, y + 26, box_w, 14, "#0f2f4f", rx=0)
    c.text(x + box_w / 2, y + 26, name, 14.5, "#ffffff", "bold", anchor="middle")
    ty = c.wrap(x + 12, y + 62, cmd, 10.5, box_w - 24, fill="#1d4ed8", family=MONO, leading=14)
    ty = c.wrap(x + 12, ty + 10, what, 11.5, box_w - 24, fill="#334155", leading=15)
    c.line(x + 12, ty + 2, x + box_w - 12, ty + 2, stroke="#e2e8f0", width=1)
    c.wrap(x + 12, ty + 20, guarantee, 11.5, box_w - 24, fill="#15803d", leading=15)
    if i:
        c.path(f"M {x - 15:.1f} {y + 14:.1f} L {x - 4:.1f} {y + 20:.1f} "
               f"L {x - 15:.1f} {y + 26:.1f} z", stroke="none", fill="#64748b")
y += box_h + 22
c.text(M, y, "every command of the tool", 12.5, "#64748b")
y = c.chip_row(M, y + 12, [f"wikidata {k}" for k in COMMANDS], RIGHT,
               fill="#f8fafc", stroke="#cbd5e1", colour="#0f172a", size=12, height=26,
               pad=12, family=MONO) + 34

# ====================== 4. the compiled corpus ==============================
y = section(y, "Wikidata itself, compiled to Lean and re-checked",
            "fragments queried from the live API, stored in data/, compiled into "
            "RequestProject/Generated/")

frag = [("DouglasAdams", "douglas", "Q42"),
        ("UpperOntology", "upper", "entity, class, metaclass"),
        ("Geography", "geography", "city, country, Berlin, Paris"),
        ("CreativeWorks", "creative", "film, book, Hitchhiker's Guide"),
        ("Science", "science", "Einstein, Darwin, Lovelace"),
        ("Technology", "technology", "software, computer, Python, AI"),
        ("Mathematics", "mathematics", "mathematics, theorem, pi"),
        ("LifeSciences", "life", "organism, taxon, animal, gene"),
        ("Society", "society", "organization, business, university"),
        ("Chemistry", "chemistry", "element, compound, disease, drug"),
        ("Events", "events", "occurrence, event, war"),
        ("Core", "core", "the eleven fragments, merged and deduplicated"),
        ("Structures", "structures", "the notions the library is made of: pullback, retract, monoid"),
        ("RelatedStructures", "related", "sheaf, presheaf, natural transformation, homeomorphism"),
        ("RelatedStructures2", "related2", "topos, cartesian closed category, equaliser, pushout"),
        ("VocabularyCorpus", "vocabulary", "every notion Vocabulary.lean names"),
        ("KnowledgeRepresentation", "knowledge", "OWL, RDF Schema, SKOS, SPARQL, description logic"),
        ("Theories", "theories", "the seven theories around the pullback"),
        ("Enriched", "enriched", "the theory corpus, grown by the enrichment loop"),
        ("Frontier", "frontier", "round 1: the items the crawl had not asked about"),
        ("Frontier2", "frontier2", "round 2"),
        ("Frontier3", "frontier3", "round 3"),
        ("Frontier4", "frontier4", "round 4: the last 18 items, leaving 14")]
maxfacts = max(DERIVED[m]["derivedSub"] + DERIVED[m]["derivedInst"] for m, _, _ in frag)
rowh = 26
c.rect(M, y - 4, CW, 26 + rowh * len(frag) + 12, "#ffffff", rx=12, stroke="#e2e8f0")
hdr = y + 16
c.text(M + 16, hdr, "fragment", 12, "#64748b", "bold")
c.text(M + 190, hdr, "seeds", 12, "#64748b", "bold")
c.text(M + 640, hdr, "items", 12, "#64748b", "bold", anchor="end")
c.text(M + 730, hdr, "P279 / P31", 12, "#64748b", "bold", anchor="end")
c.text(RIGHT - 16, hdr, "entailed subclass of + instance of", 12, "#64748b", "bold", anchor="end")
for i, (mod, kb, seeds) in enumerate(frag):
    yy = hdr + 22 + i * rowh
    k, d = CORP[kb], DERIVED[mod]
    total = d["derivedSub"] + d["derivedInst"]
    bold = "bold" if mod == "Core" else "normal"
    if mod == "Core":
        c.rect(M + 8, yy - 15, CW - 16, rowh - 2, "#f1f5f9", rx=6)
    c.text(M + 16, yy, mod, 12.5, "#0f172a", bold, family=MONO)
    c.text(M + 190, yy, seeds, 12, "#64748b")
    c.text(M + 640, yy, str(k["items"]), 12.5, "#0f172a", bold, anchor="end")
    c.text(M + 730, yy, f"{k['sub']} / {k['inst']}", 12.5, "#0f172a", bold, anchor="end")
    bw = max(3, 300 * total / maxfacts)
    c.rect(M + 760, yy - 11, bw, 13, "url(#g1)" if mod != "Core" else "url(#g4)", rx=6)
    c.text(RIGHT - 16, yy, f"{d['derivedSub']} + {d['derivedInst']}", 12.5, "#0f172a", bold,
           anchor="end")
y = hdr + 22 + rowh * len(frag) + 18
allkb = CORP["all"]
c.wrap(M, y, f"data/all.wdkb merges every fragment above into one base of {allkb['items']} items, "
             f"{allkb['sub']} subclass of and {allkb['inst']} instance of statements: it is what "
             "the defect report, the term table and the periodicity search run over.",
       11.5, CW, fill="#64748b", leading=15)
y += 30

findings = [
    ("A genuine ontology", "#16a34a",
     "The Douglas Adams fragment passes every check, so the whole abstract theory applies to "
     "the downloaded data: it is an Ontology in the sense of Core.lean."),
    ("A real cycle in live Wikidata", "#b91c1c",
     "Geography states region \u2291 geographical area and geographical area \u2291 region. Proved: "
     "no ontology can have exactly those P279 statements."),
    ("Merging really adds knowledge", "#1d4ed8",
     f"The corpus entails {GAIN['derivedSub']} subclass of and {GAIN['derivedInst']} instance of "
     "facts no single fragment does - and loses nothing: every fragment statement still follows."),
]
fw = (CW - 2 * 14) / 3
for i, (t, col, body) in enumerate(findings):
    x = M + i * (fw + 14)
    c.rect(x, y, fw, 108, "#ffffff", rx=13, stroke="#cbd5e1")
    c.rect(x, y, 5, 108, col, rx=2.5)
    c.text(x + 18, y + 28, t, 15, "#0f172a", "bold")
    c.wrap(x + 18, y + 50, body, 12, fw - 36, fill="#475569", leading=16)
y += 108 + 36

# ====================== 5. where the results sit ============================
y = section(y, "Where the results sit", "theorems and lemmas per layer of the development")

layers = LAYERS

grads = ["url(#g1)", "url(#g2)", "url(#g3)", "url(#g4)", "url(#g5)"]
maxv = max(n for _, _, _, n in layers)
for i, (name, mods, note, n) in enumerate(layers):
    shown = [m for m in mods if not m.startswith("Generated/")]
    txt = " \u00b7 ".join(shown + ([note] if note else []))
    rows = len(wrap_lines(txt, 11.5, 560, family=MONO))
    rowh = 42 + 15 * rows
    c.rect(M, y, CW, rowh, "#ffffff", rx=12, stroke="#e2e8f0")
    c.text(M + 18, y + 26, name, 15.5, "#0f172a", "bold")
    c.wrap(M + 18, y + 46, txt, 11.5, 560, fill="#94a3b8", family=MONO, leading=15,
           max_lines=rows)
    bw = max(5, 300 * n / maxv)
    c.rect(M + 640, y + 18, bw, 16, grads[i % len(grads)], rx=8)
    c.text(RIGHT - 18, y + 31, f"{n} theorems", 14, "#0f172a", "bold", anchor="end")
    y += rowh + 9
y += 26

# ====================== 6. the ontology as mathematics ======================
y = section(y, "The ontology as mathematics",
            "three layers that treat the ontology itself as a mathematical object, each "
            "grounded in the Wikidata article that names it")

maths = [
    ("Category theory, topology, type theory", "url(#g3)", "#6d28d9",
     "Q217413 category theory · Q42989 topology · Q1062242 Grothendieck topology",
     ["ontologies and strict morphisms are a category; the fibre product is a pullback "
      "square, and every cospan has one",
      "a class hierarchy is a space, a strict morphism is exactly a continuous map, and "
      "the fibre product is the pullback in TopCat",
      "jointly surjective alignments are a pretopology, so a Grothendieck topology, and "
      "labellings are a sheaf on that site",
      "the same pullback again as a homotopy fibre product, and cube by cube",
      "the automorphism group of an ontology, and class extensions as a GF(2) vector space"]),
    ("Periodicity and the spectrum", "url(#g4)", "#c2410c",
     "the class hierarchy of the downloaded corpus, searched for cycles",
     ["a computable shortest-period search, proved correct and minimal, with phase "
      "certificates that make a component period exact",
      "over the whole corpus: eleven periodic items, 1567 aperiodic, four components "
      "with periods 2, 2, 3 and 4",
      "every relation of the ontology layer read as an operator: which words close, and "
      "with what phase",
      "minimum feedback edge and vertex sets: how far the hierarchy is from acyclic",
      "the repaired hierarchy of the defect report has no periodic point at all"]),
    ("The algebra of transformations", "url(#g1)", "#1d4ed8",
     "relation words as programs, and their grading",
     ["a Gödel numbering of the relation words: RelWord.equivNat",
      "concatenation is composition, so the words form a monoid acting on item sets",
      "the metaclass level grades the words by an integer, honestly: with inverses "
      "allowed, a forward and a backward instance of step cancel",
      "so a closing signed word of non-zero degree refutes every ontology model of a base",
      "the compiler stages act by morphisms; the cyclic part has order exactly twelve, "
      "split by the CRT as 12 = 2^2 · 3"]),
]
mcol_w = (CW - 2 * 14) / 3


def maths_height(props, facts):
    h = 56 + 17 * len(wrap_lines(props, 12.5, mcol_w - 36, family=MONO)) + 6
    for f in facts:
        h += 16 * len(wrap_lines(f, 12.5, mcol_w - 52)) + 2
    return h + 14


mh = max(maths_height(p_, f_) for _, _, _, p_, f_ in maths)
for i, (name, grad, colour, props, facts) in enumerate(maths):
    x = M + i * (mcol_w + 14)
    c.rect(x, y, mcol_w, mh, "#ffffff", rx=14, stroke="#cbd5e1")
    c.rect(x, y, mcol_w, 6, grad, rx=3)
    c.text(x + 18, y + 34, name, 17, "#0f172a", "bold")
    ty = c.wrap(x + 18, y + 56, props, 12.5, mcol_w - 36, fill=colour, family=MONO, leading=17)
    ty += 6
    for f in facts:
        c.circle(x + 22, ty - 4, 2.5, colour)
        ty = c.wrap(x + 32, ty, f, 12.5, mcol_w - 52, fill="#334155", leading=16)
        ty += 2
y += mh + 36

# ====================== 7. footer ===========================================
c.rect(M, y, CW, 104, "#0f172a", rx=14)
badges = [("lake build", "clean"), ("sorry / admit", str(TOT["sorries"])),
          ("axioms", "standard only"), ("by decide checks", str(TOT["decides"])),
          ("#eval demos", str(TOT["evals"])),
          ("hand-written mods", str(TOT["handwritten_modules"])),
          ("generated mods", str(TOT["generated_modules"]))]
bw2 = (CW - 40) / len(badges)
for i, (k, v) in enumerate(badges):
    xx = M + 20 + i * bw2
    c.text(xx, y + 42, k, 12.5, "#94a3b8", family=MONO)
    good = v in ("clean", "0", "standard only")
    c.text(xx, y + 72, v, 19, "#4ade80" if good else "#e2e8f0", "bold")
y += 104 + 30
c.wrap(M, y, "Every claim on this poster is a named theorem: docs/SHOWCASE.md lists them and "
             "RequestProject/Showcase.lean re-checks the list on every build. Identifiers "
             "follow Wikidata; the compiled fragments are real downloads and the theorems "
             "about them are theorems about that data, while the hand-built example fragments "
             "are stylised excerpts and the theorems about them are statements about those "
             "fragments. Regenerate with python3 docs/make_showcase_svg.py.",
       12, CW, fill="#94a3b8", leading=17)
H = y + 40

c.write(os.path.join(ROOT, "docs", "showcase.svg"), H)
print("docs/showcase.svg", W, "x", H)
