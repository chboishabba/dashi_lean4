/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Worklist
import RequestProject.Gaps
import RequestProject.Cli.ReportCmd

/-!
# `wikidata worklist` — the diagnostics as a list of things to work on

`wikidata report` writes one line per issue.  Over the whole corpus that is a
long table and a poor worklist.  This command writes the same issues *grouped*,
four ways, and one file per group:

```
wikidata worklist data/*.wdkb --out docs/reports/worklist
  → worklist/by-code.{csv,html,svg}     one task per error type
  → worklist/by-source.{csv,html,svg}   one task per file
  → worklist/by-layer.{csv,html,svg}    one task per layer of the model
  → worklist/by-status.{csv,html,svg}   one task per kind of work
  → worklist/tasks/CODE.csv             the issues of one task, on their own
  → worklist/README.md                  the index, biggest task first
```

With `--gaps` the table also carries what is *missing* rather than wrong —
parentless items, isolated items and childless classes
(`RequestProject.Gaps`), which are warnings by construction
(`Wikidata.Report.gapRows_severity`) and appear as their own `gap` layer.

Every grouping is the same set of issues seen through a different key, and the
grouping is proved to be a partition of the report
(`Wikidata.Report.tasks_flatMap_perm`), so each of the four tables accounts for
exactly the issues found, once each (`Wikidata.Report.worklist_size_sum`,
`taskBars_count_sum`).  An empty worklist is a certificate
(`Wikidata.Report.worklist_eq_nil_iff` with
`Wikidata.Report.rows_eq_nil_iff_clean`).
-/

namespace Wikidata
namespace Cli

open Report

/-- One way of splitting the report into things to work on. -/
structure Grouping where
  /-- The file name stem the three files are written under. -/
  slug : String
  /-- What the rows are grouped by. -/
  key : Report.Row → String
  /-- The name of the grouping, for the page heading. -/
  heading : String
  /-- A sentence saying what a task of this grouping is. -/
  blurb : String

/-- The four groupings the command writes. -/
def groupings : List Grouping :=
  [{ slug := "by-code", key := Report.byCode, heading := "By error type",
     blurb := "one task per kind of problem: fix them with one rule each" },
   { slug := "by-source", key := Report.bySource, heading := "By file",
     blurb := "one task per fragment of the corpus: adopt a topic" },
   { slug := "by-layer", key := Report.byLayer, heading := "By layer",
     blurb := "one task per layer of the model: ontology, series, taxon, kinship, parenting" },
   { slug := "by-status", key := Report.byStatus, heading := "By kind of work",
     blurb := "proven fixes are safe to apply, suggested fixes are mechanical, the rest need a modelling decision" }]

/-- Keeps the characters that are safe in a file name; everything else becomes
`-`.  Report keys are identifiers and dashed codes, so this only ever has to
tidy a file path used as a key. -/
def slugify (s : String) : String :=
  let ok (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_'
  let cs := s.toList.map fun c => if ok c then c else '-'
  if cs.isEmpty then "task" else String.ofList cs

/-- How many rows of a table have the given remediation status. -/
def countStatus (rows : List Report.Row) (st : Status) : ℕ :=
  (rows.filter fun r => r.status == st).length

/-- The three files of one grouping. -/
def writeGrouping (dir : String) (g : Grouping) (source : String)
    (rows : List Report.Row) : IO Unit := do
  IO.FS.createDirAll dir
  let ts := Report.worklist g.key rows
  let intro :=
    s!"{ts.length} task(s) over {rows.length} item(s) of work in {source} — {g.blurb}. " ++
    "Biggest task first; every item appears in exactly one task."
  let title := s!"Wikidata worklist — {g.heading}"
  IO.FS.writeFile (dir ++ "/" ++ g.slug ++ ".csv")
    (Report.worklistCsv g.key rows ++ "\n")
  IO.FS.writeFile (dir ++ "/" ++ g.slug ++ ".html")
    (Report.worklistHtml title intro g.heading g.key rows ++ "\n")
  IO.FS.writeFile (dir ++ "/" ++ g.slug ++ ".svg")
    (Report.worklistSvg title s!"{ts.length} task(s), {rows.length} item(s) of work" g.key rows ++ "\n")

/-- One CSV file per task of a grouping: the issues of that task on their own, so
a contributor can take a single file away.  Returns the tasks written. -/
def writeTaskFiles (dir : String) (key : Report.Row → String)
    (rows : List Report.Row) : IO (List Report.Task) := do
  let ts := Report.worklist key rows
  IO.FS.createDirAll dir
  for t in ts do
    IO.FS.writeFile (dir ++ "/" ++ slugify t.key ++ ".csv") (Report.csvOfRows t.rows ++ "\n")
  return ts

/-- The markdown line of a task in the index. -/
def taskIndexLine (t : Report.Task) : String :=
  "| [`" ++ t.key ++ "`](tasks/" ++ slugify t.key ++ ".csv) | " ++ Report.num t.size ++
    " | " ++ Report.num t.errors ++ " | " ++ Report.num t.warnings ++
    " | " ++ Report.num t.provenFixes ++ " | " ++ Report.num t.needsReview ++
    " | " ++ t.layers ++ " | " ++ t.advice ++ " |"

/-- The index page of a worklist directory. -/
def worklistIndex (source : String) (rows : List Report.Row) : String :=
  let byCode := Report.worklist Report.byCode rows
  let bySource := Report.worklist Report.bySource rows
  let head :=
    ["# What there is to work on",
     "",
     s!"Generated by `wikidata worklist {source}`: {rows.length} item(s) of work, " ++
       s!"{countSeverity rows .error} error(s) and {countSeverity rows .warning} warning(s), " ++
       s!"grouped into {byCode.length} task(s) by error type and " ++
       s!"{bySource.length} task(s) by file.",
     "",
     "Each grouping is the same set of issues under a different key, and the",
     "grouping is a proved partition of the report (`Wikidata.Report.tasks_flatMap_perm`):",
     "every item belongs to exactly one task, so the counts below add up",
     "(`Wikidata.Report.worklist_size_sum`).",
     "",
     "| grouping | table | page | chart |",
     "|---|---|---|---|"] ++
    groupings.map (fun g =>
      "| " ++ g.heading ++ " | [`" ++ g.slug ++ ".csv`](" ++ g.slug ++ ".csv) | [`" ++
        g.slug ++ ".html`](" ++ g.slug ++ ".html) | [`" ++ g.slug ++ ".svg`](" ++
        g.slug ++ ".svg) |") ++
    ["",
     "## Tasks by error type",
     "",
     "One row per kind of problem, biggest first.  The linked CSV holds just that",
     "task's issues, with the identifiers, their labels and the suggested fix.",
     "",
     "| task | items | errors | warnings | proven fix | needs review | layers | what it takes |",
     "|---|---|---|---|---|---|---|---|"] ++
    byCode.map taskIndexLine ++
    ["",
     "## Tasks by file",
     "",
     "| file | items | errors | warnings | proven fix | needs review | layers | what it takes |",
     "|---|---|---|---|---|---|---|---|"] ++
    bySource.map (fun t =>
      "| `" ++ t.key ++ "` | " ++ Report.num t.size ++ " | " ++ Report.num t.errors ++
        " | " ++ Report.num t.warnings ++ " | " ++ Report.num t.provenFixes ++
        " | " ++ Report.num t.needsReview ++ " | " ++ t.layers ++ " | " ++ t.advice ++ " |") ++
    [""]
  Cli.joinChar '\n' head

/-- Everything a worklist directory holds, for one table of rows. -/
def writeWorklist (dir : String) (source : String) (rows : List Report.Row) : IO Unit := do
  IO.FS.createDirAll dir
  for g in groupings do
    writeGrouping dir g source rows
  let _ ← writeTaskFiles (dir ++ "/tasks") Report.byCode rows
  IO.FS.writeFile (dir ++ "/README.md") (worklistIndex source rows)

end Cli
end Wikidata
