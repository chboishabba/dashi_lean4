# `wikidata` — a command line tool built on the formalisation

The formalisation ships with an executable that lets you use it from a shell:
download entities from the Wikidata API, keep them in local files, check them
against the ontology rules, and construct the facts they imply.

```
lake build wikidata          # builds ./.lake/build/bin/wikidata
./.lake/build/bin/wikidata   # prints the usage message
```

A complete, network-free tour is in [`examples/demo.sh`](../examples/demo.sh);
run it from the project root.

## Commands

| command | what it does |
|---|---|
| `wikidata fetch Q42 [Q5 …] [--depth N] [--out F] [--cache DIR] [--offline]` | downloads `Special:EntityData/<id>.json` for each id and, with `--depth N`, everything reachable from it through `instance of` / `subclass of` in `N` further steps; builds a knowledge base, checks it, and saves it with `--out`. Downloads are cached in `--cache` (default `.wikidata-cache`), so a second run — or a run with `--offline` — needs no network. |
| `wikidata import FILE.json […] [--out F] [--name N]` | the same, from local copies of that JSON |
| `wikidata check FILE.wdkb` | validates a stored base and prints one line per defect; exit status `1` if anything is wrong |
| `wikidata derive FILE.wdkb [--out F]` | lists the `subclass of` / `instance of` facts the base implies but does not state, and with `--out` writes the saturated base |
| `wikidata ask FILE.wdkb (subclass\|instance) A B` | is the statement derivable? exit status `0` for yes, `1` for no |
| `wikidata query FILE.wdkb 'ATOM' ['ATOM' …] [--select x,y]` | evaluates a conjunctive query with variables. Each argument is one atom, written `(sub\|inst\|dsub\|dinst\|ne) TERM TERM` or `class TERM`, where a term is `?name` for a variable and an item id for a constant; `sub` / `inst` use the *derived* relations, `dsub` / `dinst` only the asserted statements. `--select` chooses the reported variables and their order. Exit status `1` if there are no answers |
| `wikidata why FILE.wdkb A B` | prints a chain of asserted P279 statements from `A` to `B`, and re-checks it |
| `wikidata add FILE.wdkb (sub\|inst\|disj) A B [--out F]` | asserts a new statement, reports whether the ontology still holds up, and saves it only if it does |
| `wikidata classes FILE.wdkb Q` | the classes `Q` is an instance of, and its superclasses |
| `wikidata instances FILE.wdkb Q` | the instances of `Q` |
| `wikidata stats FILE.wdkb` | a summary: items, statements, levels, top classes, metaclasses, derivable new facts |
| `wikidata merge A.wdkb B.wdkb [C.wdkb …] [--dedup] [--out F]` | imports bases into one another and reports that nothing was lost; `--dedup` drops the repetitions that overlapping downloads produce |
| `wikidata normalize FILE.wdkb [--out F]` | drops repeated items and statements, changing no answer |
| `wikidata module FILE.wdkb Q395 [Q5 …] [--out F] [--name N]` | extracts the sub-ontology about the given items: everything reachable from them along `subclass of` / `instance of`, with the statements out of it. The module answers every `subclass of` and `instance of` question about the items it keeps exactly as the whole base does (`KB.moduleOf_isSubclassOf`, `KB.moduleOf_isInstanceOf`), never derives anything the base does not (`KB.moduleOf_isSubclassOf_le`, `KB.moduleOf_isInstanceOf_le`), and is valid whenever the base is (`KB.moduleOf_valid`) |
| `wikidata scheck FILE.skb` | validates a stored base *together with its series layer* (`follows` P155, `part of the series` P179, `series ordinal` P1545) and prints one line per defect; exit status `1` if anything is wrong |
| `wikidata report FILE [FILE …] [--out PREFIX] [--warn\|--no-warn]` | writes the diagnostics of one or more stored bases as three importable files — `PREFIX.csv` (one line per issue: source file, layer, error type, severity, remediation status, the identifiers and their labels, the problem and the suggested fix), `PREFIX.html` (a page with a summary by error type and status, then the issues) and `PREFIX.svg` (a bar chart of the counts). `.tkb` files are read with their taxon layer, everything else with its series layer; exit status `1` if anything reported on has errors. See [`docs/REPORTS.md`](REPORTS.md) |
| `wikidata worklist FILE [FILE …] [--out DIR] [--gaps] [--warn\|--no-warn]` | writes the same findings arranged as things to work on: the rows grouped by error type, by file, by layer and by kind of work, each grouping as `DIR/by-*.csv`, `DIR/by-*.html` and `DIR/by-*.svg` (biggest task first), one CSV per task under `DIR/tasks/`, and `DIR/README.md` indexing them. `--gaps` adds what is missing rather than wrong — items with no `subclass of`/`instance of` statement, items no statement mentions, classes with nothing under them. Exit status `1` if anything reported on has errors. See [`docs/REPORTS.md`](REPORTS.md) |
| `wikidata repairs FILE [FILE …] [--out DIR] [--out-base]` | proposes, for every flagged issue of a stored base, the changes that would fix it: one to four candidates each carrying the edits it would make, the reason for them, the verdict of the check and what it does to the repair debt. Written as `DIR/NAME.csv` (one line per candidate), `DIR/NAME.html` (a page with the summary on top) and `DIR/NAME.txt` (a plain text review for a talk page). A candidate is marked `proven` only when it removes its issue, adds no error and no warning the base did not already carry, and lowers the repair debt; everything else is left for a person. **Nothing is applied**; with `--out-base` the base the recommended changes would produce is written to `DIR/NAME-repaired.wdkb` for comparison. Exit status `1` if errors would remain. See [`docs/REPAIRS.md`](REPAIRS.md) |
| `wikidata fix FILE [--out F]` | suggests a repair for every issue of a stored base and applies the ones it can check: an action is performed only if the candidate answers every `subclass of` / `instance of` question about the declared items exactly as before, carries no new error, and is strictly smaller or has strictly fewer errors. Destructive decisions — which half of a cycle to cut, which item to re-level — are printed as `review` actions and left to a human. With `--out` the candidate base is written; exit status `1` if errors remain |
| `wikidata series FILE.skb Q` | prints the series `Q` belongs to, in order, from its first element, with the ordinals and `Q` marked |
| `wikidata gloss (Q64 \| P279 \| FILE.wdkb) […]` | prints what Wikidata says about each identifier — label, description, Wikidata page, English Wikipedia article, and the target if the identifier is a redirect — or does the same for every item of a stored base and reports how many are not grounded; exit status `1` if an identifier is unknown |
| `wikidata lean FILE.wdkb --module M [--out F.lean] [--kernel] [--highlights N]` | compiles the base, and everything it entails, into a Lean module that Lean re-checks; see [`docs/CORPUS.md`](CORPUS.md) |
| `wikidata publish FILE.wdkb [FILE.wdkb …] [--out DIR]` | generates the static site the project deploys everywhere at once (GitHub Pages, Vercel, Cloudflare Pages, a Hugging Face dataset and Space, Wikimedia Toolforge): a page per ontology, the data as JSON Lines and as `.wdkb`, a small JSON API, and `manifest.json` listing every file with its length, its digest and the content address of the ontology. Refuses to publish anything that would not read back unchanged, and reports the round trip for each file (`Publish.parseJsonl?_jsonlOfKB`, `Publish.length_kbRecs`, `Publish.eq_of_renderKB_eq`). See [`docs/PUBLISHING.md`](PUBLISHING.md) |
| `wikidata onepage FILE.wdkb [FILE.wdkb …] [--out F.html] [--assets DIR] [--name TITLE]` | writes the whole report as **one** self-contained HTML file: every ontology embedded verbatim as JSON Lines, the diagnostics as CSV, a query engine, SVG charts and a PNG export, with no server, no network and no second file. Refuses to write a page whose blocks do not read back (`OnePage.parseJsonl?_blockPayload_dataBlock`, `OnePage.parseDocs?_sanitize_docs`, `OnePage.scriptSafeB_sanitize`). See [`docs/ONEPAGE.md`](ONEPAGE.md) |
| `wikidata archive FILE.wdkb [--out DIR]` | builds the archive.org deposit for a base — the ontology in both formats, a manifest of lengths and digests, and the item metadata — and reports that it re-imports to the same base and that its manifest checks out (`Archive.importKB?_bundleOf`, `Archive.checkManifest_bundleOf`) |
| `wikidata unarchive DIR [--out F.wdkb]` | reads a deposit back, reports whether its two copies agree, and saves the recovered base (`Archive.importKB?_rows_only`) |
| `wikidata sync A.wdkb B.wdkb [C.wdkb …] [--out F.wdkb]` | one round of gossip between replicas: pools what they know, reports that every replica is kept and that after the round they all agree (`KB.gossip_pairwise_equiv`, `KB.gossip_entails_all`, `KB.sync_least`) |

### The page layer

These four commands work on wikitext — the pages of the project and the
templates they call; [`docs/TEMPLATES.md`](TEMPLATES.md) is the reference.

| command | what it does |
|---|---|
| `wikidata wiki templates` | prints the documented templates as a Markdown table: name, parameters, what each does, and the body. Every template in it carries a Lean proof that it is valid |
| `wikidata wiki pages [--out DIR]` | writes the imported page and the generated pages as `.wiki` files in `DIR` (default `pages`). What is written reads back as exactly the page it was written from |
| `wikidata wiki import FILE.wiki` | reads a page of wikitext and reports its size, whether it prints back to the file character for character, whether it is hygienic, whether it calls only documented templates, and which templates it calls; exit status `1` if the file is not well-formed wikitext |
| `wikidata wiki expand NAME ARG…` | expands a call to a documented template, with positional arguments and `key=value` arguments; exit status `1` if the template is not documented |

### The enrichment loop

These seven commands grow the corpus from its own sources; [`docs/ENRICHMENT.md`](ENRICHMENT.md)
explains the loop and what each stage guarantees.

| command | what it does |
|---|---|
| `wikidata sitelinks Q42989 [Q…] [--out F.tsv] [--module M]` | the Wikimedia pages about the items, in every language Wikidata records; with `--module`, compiles the table into a Lean module and checks that it is a partial bijection between items and pages |
| `wikidata scan Q42989 [Q…] --langs en,de,fr [--max-links N] [--max-cites N] [--out F.scan]` | downloads those Wikipedia articles and reduces each to a scanned source: the items its links point at, the properties of the item it is about, and the external sources it cites |
| `wikidata frontier F.scan [--base B.wdkb] [--top N]` | what the scan points at and the library does not have: the most referenced missing terms, the most used properties with no Lean predicate, and the most cited sources not yet downloaded |
| `wikidata sources F.scan [--top N] [--out F2.scan]` | downloads the most cited sources, scans them for glossary terms and for the further sources they cite, and adds them to the scan |
| `wikidata enrich F.scan --base B.wdkb [--top N] [--out F.wdkb] [--name N]` | downloads the most referenced missing terms, turns their P279 and P31 statements into candidate statements tagged with their source, and adds them to the base — conservatively, by `KB.enrich_entails` |
| `wikidata authority Q42989 [Q…] [--module M] [--name N]` | collects the external identifiers of the items — the string-valued statements whose property has a formatter URL — and checks that each property identifies the item it belongs to |
| `wikidata scanlean F.scan --module M [--out F.lean]` | compiles a scan into a Lean module, the way `lean` compiles a knowledge base |

Options: `--out FILE`, `--cache DIR`, `--offline`, `--depth N`, `--name NAME`,
`--quiet`, `--warn` / `--no-warn`, `--dedup`, `--infer-levels`, `--select x,y`
(for `query`) (recompute the
metaclass levels from the statements), `--langs L`, `--base FILE`, `--top N`,
`--max-links N`, `--max-cites N` (for the enrichment loop), and for `lean`: `--module NAME`,
`--kernel` (have the kernel check the generated module instead of compiled
evaluation) and `--highlights N`.

## The `.wdkb` file format

One record per line, fields separated by tabs:

```
name	my ontology
item	wd	Q5
level	1	wd	Q5
sub	wd	Q5	wd	Q215627
inst	wd	Q42	wd	Q5
disj	wd	Q5	wd	Q16521
```

`wd Q5` is an ordinary Wikidata item; the other identifier forms of the
formalisation are written `ont NAME`, `about …` and `lvl N`.

## The `.skb` file format: bases with a series layer

A `.skb` file is a `.wdkb` file with three extra record kinds, so every base is
also a legal series base and the two formats can be mixed freely:

```
series	wd	v2	wd	t        -- v2 is part of the series t          (P179)
follows	wd	v2	wd	v1       -- v2 follows v1                       (P155)
ord	2	wd	v2               -- v2 has series ordinal 2               (P1545)
```

`followed by` (P156) is the converse of `follows` and is therefore not stored:
the tool derives it, and `Wikidata.SKB.mem_nextL_iff` says the derivation is
exactly the converse. [`examples/trilogy.skb`](../examples/trilogy.skb) is a
small complete file.

## What is verified

The tool is a thin shell around the formalisation; each command's promise is a
theorem in the library, and every proof is machine-checked and free of `sorry`.

| command | theorem |
|---|---|
| `fetch`, `import` | `Wikidata.Cli.sub_kbOfEntities_iff`, `Wikidata.Cli.inst_kbOfEntities_iff`: the importer asserts a statement **exactly when** the source JSON carries the corresponding P279 / P31 claim — no fact is invented and none is dropped. `Wikidata.Cli.kbOfEntities_wellFormed`: what is imported is always well-formed. |
| `check` | `Wikidata.KB.errors_eq_nil_iff_valid`: the report is empty **if and only if** the base is valid. So a silent run is a certificate, and every complaint points at a genuine defect. |
| `derive` | `Wikidata.KB.newSubL_sound`, `newInstL_sound`: every constructed fact is derivable in the input. `saturate_isSubclassOf`, `saturate_isInstanceOf`: saturation is conservative — it states more but derives exactly the same. `saturate_valid`: it preserves validity. `newSubL_saturate`, `newInstL_saturate`: one pass suffices, a second finds nothing. |
| `ask` | `Wikidata.KB.isSubclassOf_iff`, `isInstanceOf_iff`: the yes/no answers are exactly the derived facts of the abstract model. |
| `query` | `Wikidata.Query.mem_eval_iff`: the bindings the evaluator returns are **exactly** the assignments of items to the query's variables that satisfy every atom in the abstract ontology of the base — nothing satisfying is missed (`eval_complete`) and nothing spurious is returned (`eval_sound`, `eval_sat`). `Wikidata.Query.eval_eq_nil_iff`: an empty answer list means the query is genuinely unsatisfiable. `Wikidata.Query.evalT_eq_eval`: the closure table the tool evaluates against changes no answer. `Wikidata.Cli.parseAtom?_showAtom`: the surface syntax round-trips. |
| `why` | `Wikidata.KB.checkSubChain_sound`: a chain that passes the check really is a derivation; `subChain?_sound`: the search only ever returns such chains. |
| `lean` | `Wikidata.Cli.subFacts_sound`, `instFacts_sound`: every fact written into the generated module really follows from the downloaded statements. `subFacts_complete`, `instFacts_complete`: nothing that follows between declared items is left out. The generated module cites these, and Lean re-checks the whole file — nothing about it is taken on trust. |
| `normalize`, `merge --dedup` | `Wikidata.KB.normalize_isSubclassOf`, `normalize_isInstanceOf`: every query is answered exactly as before. `normalize_valid`: the validator gives the same verdict. `normalize_entails`, `entails_normalize`: no knowledge is gained or lost. |
| every command, internally | `Wikidata.KB.validFast_eq`, `errorsFast_eq`, `saturateFast_eq`, `EntailsT_eq`, …: the tool evaluates a base by computing the transitive closure once into a table, and each fast check is proved equal to the definition the rest of the library reasons about. |
| `add`, `merge` | `Wikidata.KB.merge_entails_left`, `merge_entails_right`: importing loses nothing; the `Entails` check reported on screen is the certified one. |
| `scheck` | `Wikidata.SKB.report_eq_nil_iff_sValid`: the series report is empty **if and only if** the base and its series layer are valid. `Wikidata.SKB.exists_unique_origin_of_report_eq_nil`: a silent run certifies in particular that every non-empty series has exactly one first element. |
| `gloss` | `Wikidata.Grounded.lookup_unique`: the glossary is well formed, so the entry printed for an identifier is the **only** entry carrying it. `Wikidata.Grounded.corpus_covered`, `handwritten_covered`: every item of every downloaded fragment, and of every hand-built ontology of the library, has such an entry — so the command never has to answer "unknown" about the corpus. The table itself is downloaded from the Wikidata API by `scripts/fetch_glossary.py`; see [`docs/GLOSSARY.md`](GLOSSARY.md). |
| `report` | `Wikidata.Cli.reportRows_eq`: the table written to the files is exactly `Wikidata.Report.SKB.rows` of the base, one row per issue of the certified report. `Wikidata.Report.errorRows_eq_nil_iff_valid`: the error rows are empty **if and only if** the base is valid, so an empty table is a certificate. `Wikidata.Report.severity_error_count` and `bars_count_sum`: the counts in the summary and the bars of the chart add up to the rows of the table. `Wikidata.Report.parseCsvText_csvOfRows`: the CSV can be read back, field for field, into the rows it was written from — so a spreadsheet sees exactly what the validator found. `Wikidata.Report.htmlEscape_no_markup`: no identifier or label can inject markup into the page. `Wikidata.Report.provenFix_prunable`: a row whose status is `proven-fix` names a statement whose deletion keeps the base valid and changes no derived fact (`Wikidata.KB.warning_prunable`). |
| `worklist` | `Wikidata.Report.tasks_flatMap_perm` and `worklist_flatMap_perm`: the tasks are a partition of the report — put back together they are a permutation of the rows, so no issue is dropped or counted twice. `Wikidata.Report.worklist_size_sum` and `taskBars_count_sum`: the task sizes, and the bars of the chart, add up to the number of rows. `Wikidata.Report.worklist_sorted`: no task is listed before a bigger one. `Wikidata.Report.worklist_eq_nil_iff`: an empty worklist means there is nothing to do. `Wikidata.Report.Task.errors_add_warnings` and `Task.status_counts`: the severities and the three remediation statuses each account for the whole task. `Wikidata.Report.Task.automatic_rows_provenFix`: a task advertised as safe holds only fixes already proved to change no derived fact. `Wikidata.Report.gapRows_severity`: a gap is never reported as an error. `Wikidata.Report.parseCsvText_worklistCsv`: the worklist CSV reads back exactly as written. |
| `repairs` | `Wikidata.KB.reviewItems_covers`, `reviewItems_issue_flagged` and, for the series layer, `Wikidata.SKB.sReviewItems_covers`, `sReviewItems_issue_flagged`: the review has a line for every candidate repair of every flagged issue in either layer, and every line is about an issue the base really flags — no work is dropped and none is invented. `Wikidata.KB.reviewItems_honest`: the verdict, the two scores and the base after the change agree with each other, so the table reports the check that was run. `Wikidata.KB.proven_no_regression`: a line marked `proven` removes the issue it was raised for and leaves no error and no warning the base did not already carry. `Wikidata.KB.proven_scoreAfter_lt`: it also lowers the repair debt, which is why the workflow terminates (`Wikidata.KB.rounds_stabilises`). `Wikidata.KB.applyProposals_errors_subset`, `applyProposals_warnings_subset`, `applyProposals_valid`, `applyProposals_score_le`: *any* selection an editor accepts is safe, because each proposal is re-checked as it is applied. `Wikidata.KB.autofix_eq_self_of_clean`, `Wikidata.SKB.sAutofix_eq_self_of_sFlagged_nil`: a base with nothing wrong is left untouched. `Wikidata.SKB.sApplyProposals_base_errors_subset`: repairing the series layer never breaks the taxonomy underneath it. `Wikidata.KB.parseCsvText_reviewCsv`: the review CSV reads back exactly as written. `Wikidata.KB.reviewItemsFast_eq`, `autofixFast_eq`: the fast computation the tool runs is the one the theorems are about. |
| `fix` | `Wikidata.Cli.fixTrace_snd`: the base the command writes is exactly `Wikidata.KB.repair`, the certified engine of [`RequestProject/Fixes.lean`](../RequestProject/Fixes.lean) run on the suggested actions. `Wikidata.KB.applyFixes_errors_le`: a repair never introduces an error. `Wikidata.KB.applyFixes_isSubclassOf`, `applyFixes_isInstanceOf`: no fact about a declared item is gained or lost. `Wikidata.KB.applyFixes_valid`: repairing a valid base leaves a valid base. `Wikidata.KB.dropSub_mem_fixes_iff` and `status_of_dropSub_mem_fixes`: the only statement the engine deletes by itself is a redundant `subclass of` — exactly the rows the report marks `proven-fix` — and `redundant_fix_accepted` says that deletion is never refused. `Wikidata.KB.applyFixSafeFast_eq`, `suggestedFixesFast_eq`: the fast computation the tool runs is the one the theorems are about. |
| `series` | `Wikidata.SKB.mem_chainFrom_iff`: the printed enumeration contains exactly the items reachable by following `followed by` from the start, `chainFrom_nodup` that it repeats nothing, and `chainFrom_isChain` that consecutive printed items really are consecutive in the series. |
| saving and loading | `Wikidata.Cli.parseKB?_renderKB`: reading back a file the tool wrote returns **exactly** the knowledge base that was written. The tool refuses to write a base whose identifiers contain a tab or newline, which is precisely the hypothesis of that theorem. |

Metaclass levels are the one thing not fixed by the Wikidata data model, so the
importer *guesses* them (`Wikidata.Cli.inferLevels`, propagating
`level (class) = level (instance) + 1`). No theorem claims the guess is right:
instead the tool always re-runs the validator afterwards and prints what it
finds.

A worked example, checked at compile time, is in
[`RequestProject/Cli/Examples.lean`](../RequestProject/Cli/Examples.lean).

## Source layout

| file | contents |
|---|---|
| `RequestProject/Cli/Derive.lean` | new-fact construction, saturation, checked explanations |
| `RequestProject/Cli/Format.lean` | the `.wdkb` codec and its round-trip theorem |
| `RequestProject/Cli/SeriesFormat.lean` | the `.skb` codec (series records) and its round-trip theorem `Wikidata.Cli.parseSKB?_renderSKB` |
| `RequestProject/Series.lean` | the series layer: engine, validator, semantics |
| `RequestProject/SeriesChain.lean` | certified in-order enumeration of a series |
| `RequestProject/SeriesDiagnostics.lean` | the series report and its completeness theorem |
| `RequestProject/Cli/Import.lean` | Wikidata JSON → knowledge base, with faithfulness theorems |
| `RequestProject/Cli/Fetch.lean` | the `IO` layer: API downloads, caching, file reading and writing |
| `RequestProject/Cli/Tool.lean` | the commands and the executable |
| `RequestProject/Cli/Codegen.lean` | the Lean code generator and its soundness/completeness theorems |
| `RequestProject/Cli/Examples.lean` | the worked example |
| `RequestProject/Queries.lean` | the query language, its semantics and the certified evaluator |
| `RequestProject/Cli/Query.lean` | the textual query syntax and its round-trip theorem |
| `RequestProject/FastEval.lean` | closure tables: the fast checks and their equality with the originals |
| `RequestProject/Normalize.lean` | deduplication and the theorems that it changes nothing |
| `RequestProject/Generated/*.lean` | machine-generated Wikidata fragments (see [`docs/CORPUS.md`](CORPUS.md)) |
| `RequestProject/Grounding.lean` | glossaries: entries, lookup, coverage and well-formedness, with their meaning theorems |
| `RequestProject/Generated/Glossary.lean` | the downloaded glossary: every Wikidata entity this development names |
| `RequestProject/Vocabulary.lean` | the notions of the formalisation, each paired with the Wikidata entity it formalises |
| `RequestProject/Grounded.lean` | the grounding checks: the glossary is well formed, covers the corpus, and confirms the vocabulary |
| `RequestProject/CompiledFacts.lean` | hand-written reasoning on top of the generated fragments |
| `RequestProject/CorpusEntailment.lean` | the merged corpus entails every fragment it was built from |
| `RequestProject/Worklist.lean` | the worklist: report rows grouped into tasks, sorted, with the partition and size theorems, and the CSV/HTML/SVG renderers |
| `RequestProject/Gaps.lean` | gaps: parentless, isolated and childless-class leads, turned into report rows |
| `RequestProject/Cli/WorklistCmd.lean` | the `worklist` command: groupings, per-task files and the index |
| `RequestProject/RepairWorkflow.lean` | the repair workflow: the edit vocabulary, the repair debt, the candidate repairs for every issue, the check that certifies one, and applying a selection |
| `RequestProject/RepairReview.lean` | the patch review: one reviewable line per candidate, with the CSV, HTML and plain text renderers and their honesty theorems |
| `RequestProject/RepairExamples.lean` | the workflow run, in Lean, on one small base per issue type and on a base carrying all eight at once |
| `RequestProject/SeriesRepair.lean` | the same workflow for the series layer, with the extra guarantee that repairing a series never breaks the taxonomy under it |
| `RequestProject/SeriesRepairExamples.lean` | the series workflow run on one small layer per series issue type |
| `RequestProject/Cli/RepairCmd.lean` | the `repairs` command: the review files and the candidate base |
| `scripts/refresh-corpus.sh` | the whole pipeline: query, import, merge, compile, check |
| `scripts/fetch_glossary.py` | downloads the glossary from the Wikidata API; `--check` reports whether every identifier used in the project is grounded, `--offline` works from the cache |
| `scripts/wd_search.py`, `scripts/wd_show.py` | small helpers for finding and inspecting Wikidata entities while grounding a new notion |
