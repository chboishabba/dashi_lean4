import RequestProject.Fixes
import RequestProject.Cli.SeriesFormat
import RequestProject.Cli.TaxaFormat
import RequestProject.Cli.Fetch

/-!
# `wikidata report` — the diagnostics as files you can open

`wikidata check` prints its findings on the terminal.  This command writes the
same findings as three files:

* `FILE.csv` — one line per issue, for a spreadsheet or a script.  Reading it
  back returns exactly the rows that were written
  (`Wikidata.Report.parseCsvText_csvText`);
* `FILE.html` — a page with a summary table by error type and status, and the
  issues below it.  Every field is escaped
  (`Wikidata.Report.htmlEscape_no_markup`);
* `FILE.svg` — a bar chart of the counts, one bar per error type, coloured by
  severity.  The bars add up to the number of issues
  (`Wikidata.Report.bars_count_sum`).

The rows come from `RequestProject.Reports`, so an empty table is a certificate
that the base is valid (`Wikidata.Report.errorRows_eq_nil_iff_valid`), and each
row carries the identifiers the issue is about together with the action
suggested for it.

`Wikidata.Cli.reportRows_eq` says the rows this command exports are exactly the
rows the library defines: the tool computes the errors with the fast closure
table (`Wikidata.KB.errorsFast_eq`), which changes nothing.
-/

namespace Wikidata
namespace Cli

open Report

/-- The ontology rows of a base.  The errors are computed with the fast closure
table (`Wikidata.KB.errorsFast_eq`); the quadratic redundancy scan runs only when
asked for. -/
def baseReportRows (warn : Bool) (kb : KB) : List Report.Row :=
  kb.errorsFast.map rowOfIssue ++ (if warn then kb.warnings.map rowOfIssue else [])

theorem baseReportRows_eq (kb : KB) : baseReportRows true kb = Report.KB.rows kb := by
  simp [baseReportRows, Report.KB.rows, KB.errorsFast_eq]

/-- The rows the command exports for a series-layered base.  A file with no series
statements is reported on as a bare knowledge base, which by
`Wikidata.Report.SKB.rows_eq_of_no_series` reports exactly the same issues while
skipping the (quadratic) scan for cycles in the series. -/
def reportRows (warn : Bool) (s : SKB) : List Report.Row :=
  if s.series.isEmpty && s.follows.isEmpty && s.ordinals.isEmpty then
    baseReportRows warn s.base
  else
    baseReportRows warn s.base ++
      s.sErrors.map rowOfSeriesIssue ++ s.sWarnings.map rowOfSeriesIssue

/-- **What the command exports is the report of the library.** -/
theorem reportRows_eq (s : SKB) : reportRows true s = Report.SKB.rows s := by
  by_cases h : (s.series.isEmpty && s.follows.isEmpty && s.ordinals.isEmpty) = true
  · simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    rw [reportRows, if_pos (by simp [h.1.1, h.1.2, h.2]),
      Report.SKB.rows_eq_of_no_series h.1.1 h.1.2 h.2, baseReportRows_eq]
  · rw [reportRows, if_neg h, baseReportRows_eq, Report.SKB.rows, List.append_assoc]

/-- The rows exported for a taxon-layered base. -/
def taxonReportRows (warn : Bool) (k : TKB) : List Report.Row :=
  baseReportRows warn k.base ++
    k.tErrors.map rowOfTaxonIssue ++ k.tWarnings.map rowOfTaxonIssue

theorem taxonReportRows_eq (k : TKB) : taxonReportRows true k = Report.TKB.rows k := by
  rw [taxonReportRows, baseReportRows_eq, Report.TKB.rows, List.append_assoc]

/-- Reads a stored base and reports on it: `.tkb` files are read with their taxon
layer, everything else with its series layer (an ordinary `.wdkb` file reads as a
base with no series statements). -/
def rowsOfPath (path : String) (warn : Option Bool) : IO (String × List Report.Row) := do
  let raw ← IO.FS.readFile path
  let txt := if raw.endsWith "\n" then (raw.dropEnd 1).toString else raw
  if path.endsWith ".tkb" then
    match parseTKB? txt with
    | some k =>
        return (k.base.name, taxonReportRows (warn.getD (k.base.sub.length ≤ 200)) k)
    | none => throw (IO.userError s!"{path}: not a well-formed taxon file")
  else
    match parseSKB? txt with
    | some s =>
        return (s.base.name, reportRows (warn.getD (s.base.sub.length ≤ 200)) s)
    | none => throw (IO.userError s!"{path}: not a well-formed knowledge base")

/-- Reads the ontology layer of a stored base, whichever layer file it comes in:
`.tkb` and `.skb` files are read and their base taken. -/
def baseOfPath (path : String) : IO KB := do
  let raw ← IO.FS.readFile path
  let txt := if raw.endsWith "\n" then (raw.dropEnd 1).toString else raw
  if path.endsWith ".tkb" then
    match parseTKB? txt with
    | some k => return k.base
    | none => throw (IO.userError s!"{path}: not a well-formed taxon file")
  else
    match parseSKB? txt with
    | some s => return s.base
    | none => throw (IO.userError s!"{path}: not a well-formed knowledge base")

/-- Strips a known extension from a file name, to make the output prefix. -/
def stripExt (f : String) : String :=
  let drop (e : String) (s : String) : String :=
    if s.endsWith e then (s.dropEnd e.length).toString else s
  drop ".wdkb" (drop ".skb" (drop ".tkb" f))

/-- How many rows have the given severity. -/
def countSeverity (rows : List Report.Row) (sv : Severity) : ℕ :=
  (rows.filter (fun r => r.severity == sv)).length

/-- The three report files for a table of rows. -/
def writeReports (prefixPath : String) (title : String) (source : String)
    (rows : List Report.Row) : IO Unit := do
  if let some dir := (System.FilePath.mk (prefixPath ++ ".csv")).parent then
    IO.FS.createDirAll dir
  let errs := countSeverity rows .error
  let warns := countSeverity rows .warning
  let intro :=
    s!"{rows.length} issue(s) — {errs} error(s), {warns} warning(s) — found in {source}. " ++
    "Each row names the items the problem is about and the action suggested for it."
  IO.FS.writeFile (prefixPath ++ ".csv") (csvOfRows rows ++ "\n")
  IO.FS.writeFile (prefixPath ++ ".html") (htmlOfRows title intro rows ++ "\n")
  IO.FS.writeFile (prefixPath ++ ".svg")
    (svgOfRows title s!"{errs} error(s), {warns} warning(s) in {source}" rows ++ "\n")

/-! ### `wikidata fix` -/

/-- Runs the repair engine action by action, recording for each whether it was
accepted, and returning the candidate base. -/
def fixTrace (kb : KB) : List FixAction → List (FixAction × Bool) × KB
  | [] => ([], kb)
  | f :: fs =>
      let kb' := kb.applyFixSafeFast f
      let r := fixTrace kb' fs
      ((f, decide (kb' ≠ kb)) :: r.1, r.2)

/-- **The trace ends at the candidate**: what the command writes out is exactly
`Wikidata.KB.applyFixes`, hence `Wikidata.KB.repair` when it is run on the
suggested actions. -/
theorem fixTrace_snd : ∀ (fs : List FixAction) (kb : KB), (fixTrace kb fs).2 = kb.applyFixes fs
  | [], _ => rfl
  | f :: fs, kb => by
      rw [fixTrace, KB.applyFixes_cons, KB.applyFixSafeFast_eq]
      exact fixTrace_snd fs (kb.applyFixSafe f)

/-- One line of the trace is reported for each action. -/
theorem fixTrace_length : ∀ (fs : List FixAction) (kb : KB), (fixTrace kb fs).1.length = fs.length
  | [], _ => rfl
  | f :: fs, kb => by
      rw [fixTrace]
      simpa using fixTrace_length fs (kb.applyFixSafeFast f)

end Cli
end Wikidata
