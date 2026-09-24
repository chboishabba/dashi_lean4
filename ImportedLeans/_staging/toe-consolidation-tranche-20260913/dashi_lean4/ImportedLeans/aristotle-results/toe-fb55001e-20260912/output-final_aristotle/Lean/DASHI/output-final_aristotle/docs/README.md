# Status and showcase images

Two generated images summarise the project.

* **`showcase.svg`** — the poster: the five hierarchies of the ontology and what
  is proved about each, the data model around them, the tool pipeline from the
  live Wikidata API to a re-checked Lean module, the compiled corpus with what
  the real data turned out to look like, and where the results sit in the
  layering of the development.
  [`SHOWCASE.md`](SHOWCASE.md) is the companion page: it names the theorem
  behind every claim on the poster.
* **`status.svg`** — the shorter status report: headline figures, theorems per
  layer, the Wikidata features covered, the newest layers, and the verification
  status.

Both charts draw the *same* layering of the development, the one list
`LAYERS` in [`stats.py`](stats.py), so the two images cannot disagree; and both
refuse to draw if a module of `RequestProject/` is left out of it or counted
twice.

[`CORPUS.md`](CORPUS.md) is the reference for the compiled data: every fragment
downloaded from the live API, its seeds, its size, what it entails, and what the
generated modules prove about it.  [`CLI.md`](CLI.md) documents every command of
the tool, including the enrichment loop, and the two file formats.
[`THEORIES.md`](THEORIES.md) is the page behind the mathematics section of the
poster: the seven theories that meet the pullback of ontologies — category
theory, topology, Grothendieck topologies, homotopy and cubical type theory,
group theory, field theory — with the module and the theorems for each.

[`PUBLISHING.md`](PUBLISHING.md) is the deployment guide: how `wikidata publish`
builds the site, how the same directory reaches GitHub Pages, Vercel, Cloudflare
Pages, a Hugging Face dataset and Space and Wikimedia Toolforge, how the copies
are mirrored over IPFS and BitTorrent and deposited on archive.org, and what is
proved about each hop — the published rows read back as the ontology, the content
address names it, replicas converge, deposits re-import.

[`ONEPAGE.md`](ONEPAGE.md) is the page for the single file report: `wikidata
onepage` writes one self-contained HTML file carrying the whole corpus, the
diagnostics, a query engine, SVG charts and a PNG export, with no server and no
network; it lists what is proved about the file's contents and what the page
checks in the browser against the verified engine.

[`REPORTS.md`](REPORTS.md) is the page for the diagnostics you can import:
`wikidata report` writes what the validators find as CSV, HTML and SVG — one row
per issue, with its layer, error type, severity, the identifiers it is about and
the status of the fix suggested for it.  The generated reports for every
fragment of the corpus, with an index, are in [`reports/`](reports/README.md);
`scripts/make-reports.sh` regenerates them.  The same page covers
`wikidata worklist`, which arranges those findings as things to work on — grouped
by error type, by file, by layer and by kind of work, each grouping a CSV, an
HTML page and an SVG chart, with one CSV per task — generated into
[`reports/worklist/`](reports/worklist/README.md).

[`REPAIRS.md`](REPAIRS.md) is the page for the repair workflow: `wikidata
repairs` proposes, for every flagged issue, the changes that would fix it and the
reason for each, and marks the ones a check certifies — the candidate removes its
issue, adds no error and no warning, and lowers the repair debt.  Nothing is
applied; the review is a CSV table, an HTML page and a plain text page for a talk
page, so a person decides.  The generated reviews are in
[`repairs/`](repairs/README.md); `scripts/make-repairs.sh` regenerates them.

[`META.md`](META.md) is a written page rather than a generated one: it reviews
reduction, pullback, retraction and Frobenius, and shows how the ontology inside
the ontology is each of them.

[`MATH.md`](MATH.md) is the other written page: the mathematics articles of
Wikidata that name the notions this library is made of — `pullback`, `retract`,
`monoid`, `preorder`, `adjoint functor`, `partition of a set`, `quotient set`,
`well-founded relation`, … — each matched with the construction that
instantiates it and with the theorem that proves the match.

[`ENRICHMENT.md`](ENRICHMENT.md) is the third written page: the automatic
enrichment loop — pull every Wikimedia page of an item in every language, scan
the articles and the sources they cite, rank what is missing, absorb the most
referenced of it — what each stage guarantees, and the first run of it over the
seven theories of `THEORIES.md`.

[`PERIODICITY.md`](PERIODICITY.md) is the fourth written page: the Wikidata
terms of every entity of the downloaded corpus — labels, descriptions and
aliases — and the periodicity search over its class hierarchy, with the eleven
periodic items it finds, the exact period of each of the four cyclic components,
and the repair that removes them all.

[`SPECTRUM.md`](SPECTRUM.md) is the fifth written page: the widened periodicity
search — every relation of the ontology layer as an operator, the words in them
that close, the phase of each component, the minimum feedback edge and vertex
sets of the class hierarchy, and the label collisions laid against them.

[`PROGRAM-ALGEBRA.md`](PROGRAM-ALGEBRA.md) is the sixth written page: the
transformations of the ontology layer read as programs — a Gödel numbering of
the relation words, their composition monoid, the integer grading by metaclass
level (with inverses, so the grading is honest), the compiler pipeline acting by
morphisms, the `ZMod d` phases, and the order-twelve cyclic part.  It also says,
rung by rung, which parts of the informal `ℕ → ℤ → ℚ → ℂ → ℍ → 𝕆 → Clifford →
Bott` ladder are *not* instantiated by this development.

`GLOSSARY.md` is the third generated page: every Wikidata entity this
development names, with its label, description and English Wikipedia article,
downloaded by `scripts/fetch_glossary.py` — which also writes `data/glossary.tsv`
and the Lean module `RequestProject/Generated/Glossary.lean`.

## Regenerating them

```
python3 docs/make_showcase_svg.py     # rewrites docs/showcase.svg
python3 docs/make_status_svg.py       # rewrites docs/status.svg
python3 docs/stats.py                 # the figures both use, printed as JSON
python3 scripts/fetch_glossary.py     # rewrites GLOSSARY.md and the glossary
```

`docs/stats.py` counts everything the images show: modules, theorems,
definitions, lines, `decide` checks and `#eval` demos in `RequestProject/`; items
and statements in `data/*.wdkb`; the entailed facts listed in the generated
modules; and the commands documented in `CLI.md`.  The generators fail rather
than draw a stale chart if a module is left out of the layering or counted
twice.  `docs/svgkit.py` is the small SVG writer they share.
