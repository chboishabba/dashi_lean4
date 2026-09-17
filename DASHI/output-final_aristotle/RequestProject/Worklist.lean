/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Reports

/-!
# A worklist: the diagnostics grouped into things to work on

`RequestProject.Reports` turns every witnessed issue into one
`Wikidata.Report.Row`.  That is the right shape for a spreadsheet and the wrong
shape for a person who wants to *pick something up*: a corpus-wide report is
thousands of rows with no handle on it.

This file adds the missing half.  Rows are grouped by a key — the error type, the
file they come from, the layer of the model, the remediation status — and each
group becomes a **task**: one thing to work on, with its size, how much of it is
an error, and whether the repair is known to be safe.

The grouping is proved to be a partition:

* `Wikidata.Report.tasks_flatMap_perm` — the rows of the tasks, put back
  together, are a permutation of the rows reported: nothing is dropped and
  nothing is counted twice;
* `Wikidata.Report.tasks_size_sum` — hence the task sizes add up to the number of
  issues;
* `Wikidata.Report.taskKeys_nodup`, `mem_taskKeys_iff`, `tasks_rows_ne_nil`,
  `tasks_rows_key` — the tasks have distinct keys, there is one for every key
  that occurs, none is empty, and a task holds exactly the rows with its key.

The worklist itself is the tasks in the order they should be attacked, biggest
first (`Wikidata.Report.worklist`), and it keeps all of the above
(`worklist_flatMap_perm`, `worklist_sorted`, `worklist_eq_nil_iff`: an empty
worklist means there is nothing to do, which by
`Wikidata.Report.rows_eq_nil_iff_clean` means the base is valid and carries no
redundant statement).

The three renderers of `RequestProject.ReportFormat` are then applied to the
worklist: `worklistCsv`, `worklistHtml`, `worklistSvg`, with
`taskBars_count_sum` saying the chart again counts every issue exactly once and
`parseCsvText_worklistCsv` that the table reads back as written.
-/

namespace Wikidata
namespace Report

/-! ## Tasks -/

/-- One thing to work on: the rows of a report that share a key. -/
structure Task where
  /-- What the rows have in common: an error type, a file, a layer, a status. -/
  key : String
  /-- The issues that make up the task. -/
  rows : List Row
deriving DecidableEq, Repr, Inhabited

/-- The rows whose key is `k`. -/
def rowsWithKey (key : Row → String) (rows : List Row) (k : String) : List Row :=
  rows.filter fun r => key r == k

/-- The keys that occur, in the order of their first occurrence. -/
def taskKeys (key : Row → String) (rows : List Row) : List String :=
  (rows.map key).dedup

/-- The tasks of a report: one per key that occurs. -/
def tasks (key : Row → String) (rows : List Row) : List Task :=
  (taskKeys key rows).map fun k => { key := k, rows := rowsWithKey key rows k }

/-- **The tasks have distinct keys.** -/
theorem taskKeys_nodup (key : Row → String) (rows : List Row) :
    (taskKeys key rows).Nodup :=
  List.nodup_dedup _

/-- **There is a task for exactly the keys that occur.** -/
theorem mem_taskKeys_iff {key : Row → String} {rows : List Row} {k : String} :
    k ∈ taskKeys key rows ↔ ∃ r ∈ rows, key r = k := by
  simp [taskKeys, List.mem_dedup]

theorem tasks_keys (key : Row → String) (rows : List Row) :
    (tasks key rows).map Task.key = taskKeys key rows := by
  simp [tasks, Function.comp_def]

/-- **A task holds exactly the rows with its key.** -/
theorem tasks_rows_key {key : Row → String} {rows : List Row} {t : Task}
    (ht : t ∈ tasks key rows) : ∀ r ∈ t.rows, key r = t.key := by
  obtain ⟨k, _, rfl⟩ := List.mem_map.1 ht
  intro r hr
  have := (List.mem_filter.1 hr).2
  simpa using this

/-- **No task is empty**: every task has something in it to work on. -/
theorem tasks_rows_ne_nil {key : Row → String} {rows : List Row} {t : Task}
    (ht : t ∈ tasks key rows) : t.rows ≠ [] := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.1 ht
  obtain ⟨r, hr, hrk⟩ := mem_taskKeys_iff.1 hk
  exact List.ne_nil_of_mem (a := r) (List.mem_filter.2 ⟨hr, by simp [hrk]⟩)

/-- The partition lemma: over a repetition-free list of keys covering every row,
the rows selected key by key are, put back together, a permutation of the rows. -/
theorem flatMap_rowsWithKey_perm (key : Row → String) :
    ∀ (keys : List String) (rows : List Row), keys.Nodup → (∀ r ∈ rows, key r ∈ keys) →
      (keys.flatMap (rowsWithKey key rows)).Perm rows := by
  intro keys
  induction keys with
  | nil =>
      intro rows _ h
      have : rows = [] := by
        rcases rows with _ | ⟨r, rs⟩
        · rfl
        · exact absurd (h r List.mem_cons_self) (by simp)
      simp [this]
  | cons k ks ih =>
      intro rows hnd h
      have hkns : k ∉ ks := (List.nodup_cons.1 hnd).1
      set rest : List Row := rows.filter (fun r => !(key r == k)) with hrest
      have hcong : ∀ k' ∈ ks, rowsWithKey key rows k' = rowsWithKey key rest k' := by
        intro k' hk'
        have hne : k' ≠ k := by
          rintro rfl; exact hkns hk'
        rw [hrest, rowsWithKey, rowsWithKey, List.filter_filter]
        refine (List.filter_congr ?_).symm
        intro r _
        by_cases hrk : key r = k'
        · simp [hrk, hne]
        · simp [hrk]
      have hmemrest : ∀ r ∈ rest, key r ∈ ks := by
        intro r hr
        have h1 := List.mem_filter.1 hr
        rcases List.mem_cons.1 (h r h1.1) with hEq | hmem
        · simp [hEq] at h1
        · exact hmem
      have hIH : (ks.flatMap (rowsWithKey key rest)).Perm rest :=
        ih rest (List.nodup_cons.1 hnd).2 hmemrest
      have hks : ks.flatMap (rowsWithKey key rows) = ks.flatMap (rowsWithKey key rest) :=
        List.flatMap_congr hcong
      have hsplit : (k :: ks).flatMap (rowsWithKey key rows)
          = rows.filter (fun r => key r == k) ++ ks.flatMap (rowsWithKey key rest) := by
        simp [List.flatMap_cons, rowsWithKey, hks]
      rw [hsplit]
      refine (hIH.append_left _).trans ?_
      rw [hrest]
      simpa using List.filter_append_perm (fun r => key r == k) rows

/-- **The tasks partition the report**: their rows, put back together, are a
permutation of the rows reported — nothing is dropped, nothing is duplicated. -/
theorem tasks_flatMap_perm (key : Row → String) (rows : List Row) :
    ((tasks key rows).flatMap Task.rows).Perm rows := by
  have hflat : (tasks key rows).flatMap Task.rows
      = (taskKeys key rows).flatMap (rowsWithKey key rows) := by
    simp [tasks, List.flatMap_map]
  rw [hflat]
  refine flatMap_rowsWithKey_perm key _ rows (taskKeys_nodup key rows) ?_
  intro r hr
  exact mem_taskKeys_iff.2 ⟨r, hr, rfl⟩

/-- How big a task is: how many issues it collects. -/
def Task.size (t : Task) : ℕ := t.rows.length

/-- **The task sizes add up to the number of issues.** -/
theorem tasks_size_sum (key : Row → String) (rows : List Row) :
    ((tasks key rows).map Task.size).sum = rows.length := by
  have h := (tasks_flatMap_perm key rows).length_eq
  rw [List.length_flatMap] at h
  exact h

/-- There is a task exactly when there is an issue. -/
theorem tasks_eq_nil_iff (key : Row → String) (rows : List Row) :
    tasks key rows = [] ↔ rows = [] := by
  constructor
  · intro h
    have hlen := (tasks_flatMap_perm key rows).length_eq
    rw [h] at hlen
    simp only [List.flatMap_nil, List.length_nil] at hlen
    exact List.eq_nil_of_length_eq_zero hlen.symm
  · rintro rfl; rfl

/-! ## What a task looks like -/

/-- How many rows of the task are errors. -/
def Task.errors (t : Task) : ℕ := t.rows.countP fun r => r.severity == .error

/-- How many rows of the task are warnings. -/
def Task.warnings (t : Task) : ℕ := t.rows.countP fun r => r.severity == .warning

/-- How many rows of the task carry a fix proved not to change any derived fact. -/
def Task.provenFixes (t : Task) : ℕ := t.rows.countP fun r => r.status == .provenFix

/-- How many rows of the task carry a mechanical, but unproved, repair. -/
def Task.suggestedFixes (t : Task) : ℕ := t.rows.countP fun r => r.status == .suggestedFix

/-- How many rows of the task need a human decision. -/
def Task.needsReview (t : Task) : ℕ := t.rows.countP fun r => r.status == .needsReview

/-- **Every issue of a task is an error or a warning.** -/
theorem Task.errors_add_warnings (t : Task) : t.errors + t.warnings = t.size := by
  simp only [Task.errors, Task.warnings, Task.size]
  induction t.rows with
  | nil => rfl
  | cons r rs ih => cases hsev : r.severity <;> simp [hsev] at ih ⊢ <;> omega

/-- **Every issue of a task has exactly one remediation status.** -/
theorem Task.status_counts (t : Task) :
    t.provenFixes + t.suggestedFixes + t.needsReview = t.size := by
  simp only [Task.provenFixes, Task.suggestedFixes, Task.needsReview, Task.size]
  induction t.rows with
  | nil => rfl
  | cons r rs ih => cases hst : r.status <;> simp [hst] at ih ⊢ <;> omega

/-- A task is *automatic* when every one of its issues has a fix that is proved
not to change any derived fact. -/
def Task.automatic (t : Task) : Bool := t.rows.all fun r => r.status == .provenFix

/-- **An automatic task is safe to run**: each of its rows is a `provenFix`, so
`Wikidata.Report.provenFix_prunable` applies to it — deleting the statement the
row names keeps the base valid and changes no derived fact. -/
theorem Task.automatic_rows_provenFix {t : Task} (h : t.automatic = true) :
    ∀ r ∈ t.rows, r.status = .provenFix := by
  intro r hr
  have := (List.all_eq_true.1 h) r hr
  simpa using this

/-- The advice printed for a task: what a contributor can expect of it. -/
def Task.advice (t : Task) : String :=
  if t.automatic then
    "safe: every fix is proved to change no derived fact (`wikidata fix`)"
  else if t.needsReview == 0 then
    "mechanical: every row has a straightforward suggested edit"
  else if t.provenFixes + t.suggestedFixes == 0 then
    "by hand: every row needs a modelling decision"
  else
    "mixed: part mechanical, part modelling decision"

/-- The values a field takes over the rows of a task, without repetitions. -/
def Task.valuesOf (t : Task) (f : Row → String) : String :=
  String.intercalate " " ((t.rows.map f).dedup.filter fun s => s ≠ "")

/-- The layers a task touches. -/
def Task.layers (t : Task) : String := t.valuesOf Row.layer

/-- The error types a task collects. -/
def Task.codes (t : Task) : String := t.valuesOf Row.code

/-- The files a task spans. -/
def Task.sources (t : Task) : String := t.valuesOf Row.source

/-- One of the issues, as an example of what the task looks like. -/
def Task.sample (t : Task) : String :=
  match t.rows with
  | [] => ""
  | r :: _ => if r.object == "" then r.subject else r.subject ++ " → " ++ r.object

/-- The severity of a task: an error if any of its issues is one. -/
def Task.severity (t : Task) : Severity := if 0 < t.errors then .error else .warning

/-! ## The worklist -/

/-- Work on the biggest task first.  This is transitive and total, so sorting by
it is a genuine sort, and insertion sort keeps tasks of equal size in the order
their keys first occurred in. -/
def bySize (a b : Task) : Prop := b.size ≤ a.size

instance : DecidableRel bySize := fun _ _ => inferInstanceAs (Decidable (_ ≤ _))

instance : Std.Total bySize := ⟨fun a b => Nat.le_total b.size a.size⟩

instance : IsTrans Task bySize := ⟨fun _ _ _ hab hbc => le_trans hbc hab⟩

/-- The tasks in the order they should be attacked: biggest first. -/
def worklist (key : Row → String) (rows : List Row) : List Task :=
  List.insertionSort bySize (tasks key rows)

/-- **The worklist is the tasks, reordered.** -/
theorem worklist_perm (key : Row → String) (rows : List Row) :
    (worklist key rows).Perm (tasks key rows) :=
  List.perm_insertionSort _ _

/-- **The worklist is sorted**: no task comes before a bigger one. -/
theorem worklist_sorted (key : Row → String) (rows : List Row) :
    (worklist key rows).Pairwise bySize :=
  List.pairwise_insertionSort _ _

/-- **The worklist still partitions the report.** -/
theorem worklist_flatMap_perm (key : Row → String) (rows : List Row) :
    ((worklist key rows).flatMap Task.rows).Perm rows :=
  ((worklist_perm key rows).flatMap_right _).trans (tasks_flatMap_perm key rows)

/-- **The worklist sizes add up to the number of issues.** -/
theorem worklist_size_sum (key : Row → String) (rows : List Row) :
    ((worklist key rows).map Task.size).sum = rows.length := by
  have h := (worklist_flatMap_perm key rows).length_eq
  rw [List.length_flatMap] at h
  exact h

/-- **An empty worklist means there is nothing to do.**  Together with
`Wikidata.Report.rows_eq_nil_iff_clean` this says: no tasks exactly when the base
is valid and carries no redundant statement. -/
theorem worklist_eq_nil_iff (key : Row → String) (rows : List Row) :
    worklist key rows = [] ↔ rows = [] := by
  constructor
  · intro h
    have hlen := (worklist_flatMap_perm key rows).length_eq
    rw [h] at hlen
    simp only [List.flatMap_nil, List.length_nil] at hlen
    exact List.eq_nil_of_length_eq_zero hlen.symm
  · rintro rfl; rfl

/-- The rows of a report, reordered task by task: the issues of the biggest task
first.  This is the order the worklist page lists them in. -/
def worklistRows (key : Row → String) (rows : List Row) : List Row :=
  (worklist key rows).flatMap Task.rows

theorem worklistRows_perm (key : Row → String) (rows : List Row) :
    (worklistRows key rows).Perm rows := worklist_flatMap_perm key rows

/-! ## The keys one can group by -/

/-- Group by error type: one task per kind of problem. -/
def byCode : Row → String := Row.code

/-- Group by file: one task per fragment of the corpus. -/
def bySource : Row → String := Row.source

/-- Group by layer of the model: ontology, series, taxon, kinship, parenting. -/
def byLayer : Row → String := Row.layer

/-- Group by remediation status: what kind of work it is. -/
def byStatus (r : Row) : String := r.status.text

/-! ## The three files -/

/-- The same page as `Wikidata.Report.htmlText`, with the two section headings
chosen by the caller: a worklist page summarises by task, not by error type.
`Wikidata.Report.htmlSections_eq_htmlText` says it is the same page builder. -/
def htmlSections (title : String) (intro : String) (summaryTitle : String)
    (summaryHeader : List String) (summary : List (String × List String))
    (rowsTitle : String) (header : List String)
    (rows : List (String × List String)) : String :=
  Cli.joinChar '\n'
    (["<!DOCTYPE html>", "<html lang=\"en\">", "<head>", "<meta charset=\"utf-8\">",
      "<title>" ++ htmlEscape title ++ "</title>", "<style>", htmlStyle, "</style>",
      "</head>", "<body>",
      "<h1>" ++ htmlEscape title ++ "</h1>",
      "<p class=\"meta\">" ++ htmlEscape intro ++ "</p>",
      "<h2>" ++ htmlEscape summaryTitle ++ "</h2>", "<table>", htmlHeadLine summaryHeader] ++
     htmlRowLines summary ++
     ["</table>", "<h2>" ++ htmlEscape rowsTitle ++ "</h2>", "<table>", htmlHeadLine header] ++
     htmlRowLines rows ++
     ["</table>", "</body>", "</html>"])

/-- **The worklist page is the report page** with different headings: given the
headings the report uses, the two renderers agree character for character. -/
theorem htmlSections_eq_htmlText (title intro : String) (header : List String)
    (summary : List (String × List String)) (summaryHeader : List String)
    (rows : List (String × List String)) :
    htmlSections title intro "By error type" summaryHeader summary "Issues" header rows =
      htmlText title intro header summary summaryHeader rows := by
  have h1 : htmlEscape "By error type" = "By error type" := rfl
  have h2 : htmlEscape "Issues" = "Issues" := rfl
  simp [htmlSections, htmlText, h1, h2]

/-- The column headings of a worklist table. -/
def taskHeader : List String :=
  ["task", "items", "errors", "warnings", "proven-fix", "suggested-fix", "needs-review",
   "layers", "codes", "example", "what it takes"]

/-- A task as a table row, in the order of `Wikidata.Report.taskHeader`. -/
def Task.fields (t : Task) : List String :=
  [t.key, num t.size, num t.errors, num t.warnings, num t.provenFixes, num t.suggestedFixes,
   num t.needsReview, t.layers, t.codes, t.sample, t.advice]

theorem Task.fields_length (t : Task) : t.fields.length = taskHeader.length := by
  simp [Task.fields, taskHeader]

theorem Task.fields_ne_nil (t : Task) : t.fields ≠ [] := by simp [Task.fields]

/-- The worklist as a CSV table: one line per task. -/
def worklistCsv (key : Row → String) (rows : List Row) : String :=
  csvText taskHeader ((worklist key rows).map Task.fields)

/-- **A worklist file reads back exactly**: parsing the CSV returns the header
and then the fields of each task, in order. -/
theorem parseCsvText_worklistCsv {key : Row → String} {rows : List Row}
    (h : ∀ t ∈ worklist key rows, ∀ f ∈ t.fields, '\n' ∉ f.toList) :
    parseCsvText (worklistCsv key rows) =
      some (taskHeader :: (worklist key rows).map Task.fields) := by
  refine parseCsvText_csvText (by simp [taskHeader]) (by decide) ?_
  intro fs hfs
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hfs
  exact ⟨Task.fields_ne_nil t, h t ht⟩

/-- One bar per task, coloured by whether the task contains an error. -/
def taskBars (ts : List Task) : List Bar :=
  ts.map fun t => { label := t.key, count := t.size, colour := t.severity.colour }

/-- **The chart counts every issue exactly once**: the bars of the worklist add
up to the number of issues. -/
theorem taskBars_count_sum (key : Row → String) (rows : List Row) :
    ((taskBars (worklist key rows)).map Bar.count).sum = rows.length := by
  have h : (taskBars (worklist key rows)).map Bar.count
      = (worklist key rows).map Task.size := by
    simp [taskBars, Function.comp_def]
  rw [h, worklist_size_sum]

/-- The worklist as an SVG bar chart: one bar per task, biggest first. -/
def worklistSvg (title : String) (subtitle : String) (key : Row → String)
    (rows : List Row) : String :=
  svgText title subtitle (taskBars (worklist key rows))

/-- The worklist as an HTML page: the tasks in the order to attack them, then the
issues themselves, task by task. -/
def worklistHtml (title : String) (intro : String) (heading : String)
    (key : Row → String) (rows : List Row) : String :=
  htmlSections title intro heading taskHeader
    ((worklist key rows).map fun t => (t.severity.text, t.fields))
    "Issues, task by task" header
    ((worklistRows key rows).map fun r => (r.severity.text, r.fields))

/-- **The page lists every issue exactly once**, in worklist order. -/
theorem worklistHtml_rows_length (key : Row → String) (rows : List Row) :
    ((worklistRows key rows).map fun r => (r.severity.text, r.fields)).length = rows.length := by
  simp [(worklistRows_perm key rows).length_eq]

end Report
end Wikidata
