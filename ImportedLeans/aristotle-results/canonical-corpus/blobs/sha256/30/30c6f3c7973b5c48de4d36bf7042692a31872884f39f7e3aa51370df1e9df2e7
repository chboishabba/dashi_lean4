# Reports you can import: CSV, HTML and SVG

`wikidata check` prints its findings on the terminal, one line per defect.  That
is fine for a single run and useless for a worklist.  `wikidata report` writes
the same findings as three files:

```
wikidata report data/core.wdkb --out docs/reports/core
  → docs/reports/core.csv    one line per issue
  → docs/reports/core.html   a page: summary by error type, then the issues
  → docs/reports/core.svg    a bar chart of the counts, coloured by severity
```

Several files can be reported on at once, and then every row records which file
it came from:

```
wikidata report data/*.wdkb --out docs/reports/corpus
```

The generated reports for the whole downloaded corpus are in
[`reports/`](reports/README.md), with an index listing every fragment, how many
issues it has and of which kinds.  `scripts/make-reports.sh` regenerates them.

## What a row says

| column | what it holds |
|---|---|
| `source` | the file the issue was found in |
| `layer` | `ontology`, `series`, `taxon`, `kinship` or `parenting` |
| `code` | the error type, e.g. `subclass-cycle`, `rank-inversion` |
| `severity` | `error` — the base is not valid — or `warning` — a matter of style |
| `status` | what can be done: `proven-fix`, `suggested-fix` or `needs-review` |
| `subject`, `object`, `extra` | the witnesses: the identifiers the issue is about |
| `subject label`, `object label` | what Wikidata calls them, from the downloaded glossary |
| `message` | the problem, in a sentence |
| `fix` | the action suggested for it |

The **status** column is the remediation half of the report:

* `proven-fix` — a fix is known *and proved* not to change anything derivable.
  Today this is the redundant `subclass of` statement: `Wikidata.KB.warning_prunable`
  says deleting it keeps the base valid and changes no derived `subclass of` or
  `instance of` fact, and `Wikidata.Report.provenFix_prunable` reads that
  guarantee off the report row.
* `suggested-fix` — the repair is mechanical (declare the item the statement
  points at, or delete the statement) but it is a change to the data, so it is
  proposed, not proved.
* `needs-review` — the repair is destructive or ambiguous: which half of a cycle
  to cut, which of two parents to keep, which item to re-level.  Metaclass level
  shifts in particular propagate down a whole branch, so the tool never suggests
  one as automatic.

## The error types

| layer | codes |
|---|---|
| ontology | `dangling-sub`, `dangling-inst`, `dangling-disj`, `level-inst`, `level-sub`, `subclass-cycle`, `disjoint-violation`, `redundant-sub` |
| series | `dangling-series`, `dangling-follows`, `dangling-ordinal`, `self-follows`, `series-cycle`, `forked-series`, `series-mismatch`, `taxonomic-follows`, `ordinal-conflict` |
| taxon | `dangling-parent-taxon`, `dangling-rank`, `dangling-taxon-name`, `self-parent-taxon`, `taxon-cycle`, `multiple-parent-taxa`, `rank-inversion`, `duplicate-taxon-name`, `taxonomic-parent`, `missing-rank` |
| kinship | `dangling-father`, `dangling-mother`, `dangling-spouse`, `two-fathers`, `two-mothers`, `ancestry-cycle`, `self-spouse`, `kin-class-confusion` |
| parenting | `dangling-parenthood`, `dangling-spouse`, `self-parent`, `untyped-genetic-parent`, `two-genetic-parents`, `ancestry-cycle`, `self-spouse`, `parent-class-confusion`, `unsupported-stepparent` |

The kinship and parenting layers have no on-disk file format, so the command
line tool reports on the first three; the rows for all five are in the library
(`Wikidata.Report.rowOfKinIssue`, `rowOfParentIssue`) and can be exported from
Lean with the same three renderers.

Two hand-written example files carry one of each kind of problem, so every error
type appears in the generated reports:
[`examples/defects.skb`](../examples/defects.skb) (ontology and series) and
[`examples/taxa-defects.tkb`](../examples/taxa-defects.tkb) (taxa).

## What is verified about the files themselves

| claim | theorem |
|---|---|
| an empty error table means the base is valid — silence is a certificate, not an omission | `Wikidata.Report.errorRows_eq_nil_iff_valid`, `rows_eq_nil_iff_clean` |
| the table is a faithful copy of the diagnostics: one `error` row per error, one `warning` row per warning | `Wikidata.Report.severity_error_count` |
| what the command exports is what the library defines | `Wikidata.Cli.reportRows_eq`, `taxonReportRows_eq` |
| skipping the series scan on a base with no series statements loses nothing | `Wikidata.Report.SKB.rows_eq_of_no_series` |
| a `proven-fix` row really can be fixed: the deletion it names keeps the base valid and changes no derived fact | `Wikidata.Report.provenFix_prunable` |
| the CSV file reads back **exactly** as written — a spreadsheet import cannot mangle it | `Wikidata.Report.parseCsvText_csvText`, `parseCsvText_csvOfRows`, `parseCsvRow_csvRow` |
| no identifier can inject markup into the HTML page | `Wikidata.Report.htmlEscape_no_markup` |
| the page has exactly one row per issue | `Wikidata.Report.htmlRowLines_length` |
| the chart draws one bar per error type, and the bars add up to the number of issues | `Wikidata.Report.svgBarLines_length`, `bars_count_sum` |

## The worklist: the same issues, grouped into things to work on

A corpus-wide report is one line per issue and no handle on where to start.
`wikidata worklist` writes the same issues **grouped**, four ways at once:

```
wikidata worklist data/*.wdkb examples/defects.skb --out docs/reports/worklist
  → worklist/by-code.{csv,html,svg}     one task per error type
  → worklist/by-source.{csv,html,svg}   one task per file — adopt a topic
  → worklist/by-layer.{csv,html,svg}    one task per layer of the model
  → worklist/by-status.{csv,html,svg}   one task per kind of work
  → worklist/tasks/CODE.csv             the issues of a single task, on their own
  → worklist/README.md                  the index, biggest task first
```

The generated worklist for the corpus is in
[`reports/worklist/`](reports/worklist/README.md); `scripts/make-reports.sh`
regenerates it along with the reports.

A **task** is all the rows sharing one key.  Each line of a worklist table says

| column | what it holds |
|---|---|
| `task` | the key: an error type, a file, a layer, or a remediation status |
| `items`, `errors`, `warnings` | how big the task is, and how much of it breaks validity |
| `proven-fix`, `suggested-fix`, `needs-review` | how the work splits by remediation status |
| `layers`, `codes` | which layers and error types the task touches |
| `example` | one of the issues, as a taste of the rest |
| `what it takes` | `safe` (every fix is proved lossless), `mechanical`, `by hand`, or `mixed` |

A task is *safe* only when every one of its issues carries a `proven-fix`, and
then `Wikidata.Report.Task.automatic_rows_provenFix` together with
`Wikidata.Report.provenFix_prunable` is the guarantee: deleting the statements it
names keeps every base valid and changes no derived fact.

### Work that is not a defect: `--gaps`

A base can be perfectly valid and still be full of things to do.  With `--gaps`
the worklist also carries what the base does not *say*, in three kinds:

| code | what it is | what to do |
|---|---|---|
| `no-parent` | a declared item with no `subclass of` (P279) and no `instance of` (P31) statement | download it, or place it in the hierarchy |
| `isolated` | a declared item that occurs in no statement at all | crawl it, or drop the declaration |
| `childless-class` | a declared class with no instances and no subclasses here | download its instances, or check that it is a class |

These are warnings by construction (`Wikidata.Report.gapRows_severity`): a gap
never claims the base is broken.  Their meaning is fixed by
`Wikidata.KB.mem_rootlessL_iff`, `Wikidata.KB.mem_isolatedL_iff` and
`Wikidata.KB.mem_childlessClassL_iff`, an isolated item is proved to be
parentless as well (`Wikidata.KB.isolated_mem_rootlessL`), and an empty gap table
is again a certificate (`Wikidata.Report.gapRows_eq_nil_iff`).  They appear in
the tables under their own `gap` layer.

### What is verified about the grouping

| claim | theorem |
|---|---|
| the tasks are a partition of the report — every issue is in exactly one task, none is dropped or duplicated | `Wikidata.Report.tasks_flatMap_perm`, `worklist_flatMap_perm` |
| the task sizes add up to the number of issues | `Wikidata.Report.tasks_size_sum`, `worklist_size_sum` |
| the tasks have distinct keys, one for each key that occurs, and none is empty | `Wikidata.Report.taskKeys_nodup`, `mem_taskKeys_iff`, `tasks_rows_ne_nil` |
| a task holds exactly the rows with its key | `Wikidata.Report.tasks_rows_key` |
| the worklist is sorted: no task before a bigger one | `Wikidata.Report.worklist_sorted` |
| an empty worklist means there is nothing to do | `Wikidata.Report.worklist_eq_nil_iff` with `rows_eq_nil_iff_clean` |
| the errors and warnings of a task, and its three statuses, each account for all of it | `Wikidata.Report.Task.errors_add_warnings`, `Task.status_counts` |
| the chart's bars add up to the number of issues | `Wikidata.Report.taskBars_count_sum` |
| the worklist CSV reads back exactly as written | `Wikidata.Report.parseCsvText_worklistCsv` |
| the page lists every issue exactly once, in worklist order | `Wikidata.Report.worklistHtml_rows_length` |
| a task called safe really is: each of its issues has a fix proved lossless | `Wikidata.Report.Task.automatic_rows_provenFix` |

Worked examples of all of this, checked when the project is built, are in
[`RequestProject/ReportExamples.lean`](../RequestProject/ReportExamples.lean):
the report of a deliberately broken base, its error types, its CSV round trip,
and the one warning whose fix is proved lossless — applied, leaving an empty
report.
