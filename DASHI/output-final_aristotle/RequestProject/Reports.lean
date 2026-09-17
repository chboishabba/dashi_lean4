/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.ReportFormat
import RequestProject.Diagnostics
import RequestProject.SeriesDiagnostics
import RequestProject.TaxaDiagnostics
import RequestProject.KinshipDiagnostics
import RequestProject.ParentingDiagnostics
import RequestProject.Cli.Query

/-!
# One report table for every diagnostic layer

Each layer of the library reports *witnessed* issues: `Wikidata.Issue` for the
ontology itself, `Wikidata.SeriesIssue`, `Wikidata.TaxonIssue`,
`Wikidata.KinIssue` and `Wikidata.ParentIssue` for the layers on top of it.
This file puts them all into one shape — `Wikidata.Report.Row` — so that a whole
knowledge base can be exported as a single table, and then written as CSV, HTML
or SVG by `RequestProject.ReportFormat`.

Every row carries

* the **layer** and the **error type** (a short machine-readable code);
* a **severity**: `error` if the issue breaks validity, `warning` if it is a
  matter of style;
* a **status**, which is the remediation half of the report:
  * `provenFix` — a fix is known *and proved* not to change any derived fact
    (`Wikidata.KB.warning_prunable` for a redundant `subclass of` statement);
  * `suggestedFix` — the repair is mechanical (declare the missing item, or drop
    the statement that points at it) but it is a change to the data;
  * `needsReview` — the repair is destructive or ambiguous (metaclass level
    shifts, cycles, disjointness violations) and a human must choose;
* the **witnesses**: the identifiers the issue is about;
* a human sentence and a suggested action.

The main results:

* `Wikidata.Report.errorRows_eq_nil_iff_valid` — the exported error rows are
  empty exactly when the base is valid, so an empty report file is a
  certificate, not a silence;
* `Wikidata.Report.rows_eq_nil_iff_clean` — likewise for the whole table;
* `Wikidata.Report.severity_error_count` — the table has exactly one `error` row
  per error and one `warning` row per warning: nothing is dropped or reclassified;
* `Wikidata.Report.provenFix_prunable` — every row whose status is `provenFix`
  really can be fixed: deleting the statement it names keeps the base valid and
  changes no derived fact;
* `Wikidata.Report.bars_count_sum` — the bar chart's bars add up to the number of
  rows, so the picture counts every issue exactly once.
-/

namespace Wikidata
namespace Report

open Cli (qidText)

/-! ## The shape of a report row -/

/-- How bad an issue is. -/
inductive Severity where
  /-- The issue breaks validity: the base is not a certified ontology. -/
  | error
  /-- The issue is a matter of style: the base stays valid. -/
  | warning
deriving DecidableEq, Repr, Inhabited

/-- The severity, as it appears in a report file. -/
def Severity.text : Severity → String
  | .error => "error"
  | .warning => "warning"

/-- The colour of a severity in the generated chart. -/
def Severity.colour : Severity → String
  | .error => "#a4262c"
  | .warning => "#d8a200"

/-- What can be done about an issue: the remediation status. -/
inductive Status where
  /-- A fix is known and *proved* to change no derived fact. -/
  | provenFix
  /-- The repair is mechanical, but it changes the data. -/
  | suggestedFix
  /-- The repair is destructive or ambiguous: a human must choose. -/
  | needsReview
deriving DecidableEq, Repr, Inhabited

/-- The status, as it appears in a report file. -/
def Status.text : Status → String
  | .provenFix => "proven-fix"
  | .suggestedFix => "suggested-fix"
  | .needsReview => "needs-review"

/-- One line of a report: a witnessed issue together with its classification and
the action suggested for it. -/
structure Row where
  /-- Where the issue was found: the file or base it comes from.  The library
  leaves this empty; the command line tool fills it in when it reports on
  several files at once. -/
  source : String := ""
  /-- Which layer of the model the issue belongs to. -/
  layer : String
  /-- The error type, as a short machine-readable code. -/
  code : String
  /-- Does the issue break validity? -/
  severity : Severity
  /-- What can be done about it. -/
  status : Status
  /-- The first witness: the item the issue is about. -/
  subject : String
  /-- The label of the subject, when one is known.  The library leaves this
  empty; the command line tool fills it in from the downloaded glossary. -/
  subjectLabel : String := ""
  /-- The second witness, if the issue is about a pair. -/
  object : String
  /-- The label of the object, when one is known. -/
  objectLabel : String := ""
  /-- A third witness, for issues about triples. -/
  extra : String
  /-- The issue, in a sentence. -/
  message : String
  /-- The suggested remediation. -/
  fix : String
deriving DecidableEq, Repr, Inhabited

/-- The column headings of the exported table. -/
def header : List String :=
  ["source", "layer", "code", "severity", "status", "subject", "subject label", "object",
   "object label", "extra", "message", "fix"]

/-- A row as a list of fields, in the order of `Wikidata.Report.header`. -/
def Row.fields (r : Row) : List String :=
  [r.source, r.layer, r.code, r.severity.text, r.status.text, r.subject, r.subjectLabel,
    r.object, r.objectLabel, r.extra, r.message, r.fix]

theorem Row.fields_length (r : Row) : r.fields.length = header.length := by
  simp [Row.fields, header]

/-! ## From issues to rows -/

/-- A row of the ontology report. -/
def rowOfIssue : Issue → Row
  | .danglingSub a b =>
      { layer := "ontology", code := "dangling-sub", severity := .error,
        status := .suggestedFix, subject := qidText a, object := qidText b, extra := "",
        message := "`subclass of` statement with an endpoint that is not a declared item",
        fix := "declare the missing item, or delete the statement" }
  | .danglingInst a c =>
      { layer := "ontology", code := "dangling-inst", severity := .error,
        status := .suggestedFix, subject := qidText a, object := qidText c, extra := "",
        message := "`instance of` statement with an endpoint that is not a declared item",
        fix := "declare the missing item, or delete the statement" }
  | .danglingDisj c d =>
      { layer := "ontology", code := "dangling-disj", severity := .error,
        status := .suggestedFix, subject := qidText c, object := qidText d, extra := "",
        message := "disjointness declaration with an endpoint that is not a declared item",
        fix := "declare the missing item, or delete the declaration" }
  | .levelMismatchInst a c =>
      { layer := "ontology", code := "level-inst", severity := .error,
        status := .needsReview, subject := qidText a, object := qidText c, extra := "",
        message := "`instance of` whose value does not sit one metaclass level up",
        fix := "re-level one of the two items, or replace `instance of` by `subclass of`; level shifts affect the whole branch, so review by hand" }
  | .levelMismatchSub a b =>
      { layer := "ontology", code := "level-sub", severity := .error,
        status := .needsReview, subject := qidText a, object := qidText b, extra := "",
        message := "`subclass of` between items of different metaclass levels, or on an individual",
        fix := "re-level one of the two items, or replace `subclass of` by `instance of`; review by hand" }
  | .subclassCycle a b =>
      { layer := "ontology", code := "subclass-cycle", severity := .error,
        status := .needsReview, subject := qidText a, object := qidText b, extra := "",
        message := "two distinct classes are subclasses of each other",
        fix := "delete one of the two `subclass of` statements — which one is a modelling decision — then re-run `normalize`" }
  | .disjointViolation c d a =>
      { layer := "ontology", code := "disjoint-violation", severity := .error,
        status := .needsReview, subject := qidText a, object := qidText c, extra := qidText d,
        message := "an item is an instance of two classes declared disjoint",
        fix := "drop one of the two `instance of` statements, or the disjointness declaration" }
  | .redundantSubclass a b =>
      { layer := "ontology", code := "redundant-sub", severity := .warning,
        status := .provenFix, subject := qidText a, object := qidText b, extra := "",
        message := "`subclass of` statement already implied by the others",
        fix := "delete the statement (`KB.dropSub`): proved to change no derived fact and to keep the base valid" }

/-- A row of the series report. -/
def rowOfSeriesIssue : SeriesIssue → Row
  | .danglingSeries a t =>
      { layer := "series", code := "dangling-series", severity := .error,
        status := .suggestedFix, subject := qidText a, object := qidText t, extra := "",
        message := "`part of the series` (P179) statement with an undeclared endpoint",
        fix := "declare the missing item, or delete the statement" }
  | .danglingFollows a b =>
      { layer := "series", code := "dangling-follows", severity := .error,
        status := .suggestedFix, subject := qidText a, object := qidText b, extra := "",
        message := "`follows` (P155) statement with an undeclared endpoint",
        fix := "declare the missing item, or delete the statement" }
  | .danglingOrdinal a =>
      { layer := "series", code := "dangling-ordinal", severity := .error,
        status := .suggestedFix, subject := qidText a, object := "", extra := "",
        message := "`series ordinal` (P1545) on an item that is not declared",
        fix := "declare the item, or delete the ordinal" }
  | .selfFollows a =>
      { layer := "series", code := "self-follows", severity := .error,
        status := .suggestedFix, subject := qidText a, object := "", extra := "",
        message := "an item is declared to follow itself",
        fix := "delete the `follows` statement" }
  | .seriesCycle a b =>
      { layer := "series", code := "series-cycle", severity := .error,
        status := .needsReview, subject := qidText a, object := qidText b, extra := "",
        message := "two distinct items each come after the other",
        fix := "delete one of the `follows` statements — the order of the series is a modelling decision" }
  | .forkedSeries a b c =>
      { layer := "series", code := "forked-series", severity := .error,
        status := .needsReview, subject := qidText a, object := qidText b, extra := qidText c,
        message := "an item follows two different items: the series forks",
        fix := "keep one predecessor; if both are right, the two are different series" }
  | .seriesMismatch a b =>
      { layer := "series", code := "series-mismatch", severity := .error,
        status := .needsReview, subject := qidText a, object := qidText b, extra := "",
        message := "neighbours in the chain belong to different series",
        fix := "correct one of the `part of the series` statements" }
  | .taxonomicFollows a b =>
      { layer := "series", code := "taxonomic-follows", severity := .error,
        status := .suggestedFix, subject := qidText a, object := qidText b, extra := "",
        message := "`follows` between items already related by `subclass of` or `instance of`",
        fix := "delete the `follows` statement: the two are related taxonomically, not serially" }
  | .ordinalConflict a b =>
      { layer := "series", code := "ordinal-conflict", severity := .warning,
        status := .needsReview, subject := qidText a, object := qidText b, extra := "",
        message := "`series ordinal` values do not increase along a `follows` statement",
        fix := "correct the ordinals, or the `follows` statement" }

/-- A row of the taxon report. -/
def rowOfTaxonIssue : TaxonIssue → Row
  | .danglingParent a b =>
      { layer := "taxon", code := "dangling-parent-taxon", severity := .error,
        status := .suggestedFix, subject := qidText a, object := qidText b, extra := "",
        message := "`parent taxon` (P171) statement with an undeclared endpoint",
        fix := "declare the missing taxon, or delete the statement" }
  | .danglingRank a =>
      { layer := "taxon", code := "dangling-rank", severity := .error,
        status := .suggestedFix, subject := qidText a, object := "", extra := "",
        message := "`taxon rank` (P105) on an item that is not declared",
        fix := "declare the item, or delete the rank" }
  | .danglingName a =>
      { layer := "taxon", code := "dangling-taxon-name", severity := .error,
        status := .suggestedFix, subject := qidText a, object := "", extra := "",
        message := "`taxon name` (P225) on an item that is not declared",
        fix := "declare the item, or delete the name" }
  | .selfParent a =>
      { layer := "taxon", code := "self-parent-taxon", severity := .error,
        status := .suggestedFix, subject := qidText a, object := "", extra := "",
        message := "a taxon is its own parent taxon",
        fix := "delete the `parent taxon` statement" }
  | .taxonCycle a b =>
      { layer := "taxon", code := "taxon-cycle", severity := .error,
        status := .needsReview, subject := qidText a, object := qidText b, extra := "",
        message := "two distinct taxa each descend from the other",
        fix := "delete one `parent taxon` statement; the ranks say which direction is right" }
  | .multipleParents a b c =>
      { layer := "taxon", code := "multiple-parent-taxa", severity := .error,
        status := .needsReview, subject := qidText a, object := qidText b, extra := qidText c,
        message := "a taxon has two different parent taxa: the hierarchy is not a tree",
        fix := "keep the accepted classification and deprecate the other statement" }
  | .rankInversion a b =>
      { layer := "taxon", code := "rank-inversion", severity := .error,
        status := .needsReview, subject := qidText a, object := qidText b, extra := "",
        message := "`taxon rank` does not increase along a `parent taxon` statement",
        fix := "promote or demote one rank (see `TaxonRank.level`), or reverse the statement" }
  | .duplicateName a b =>
      { layer := "taxon", code := "duplicate-taxon-name", severity := .error,
        status := .needsReview, subject := qidText a, object := qidText b, extra := "",
        message := "two distinct taxa carry the same scientific name",
        fix := "a merge waiting to happen: unify the two items, or correct one name" }
  | .taxonomicParent a b =>
      { layer := "taxon", code := "taxonomic-parent", severity := .error,
        status := .suggestedFix, subject := qidText a, object := qidText b, extra := "",
        message := "`parent taxon` between items already related by `subclass of` or `instance of`",
        fix := "delete one of the two: `parent taxon` and `subclass of` say different things" }
  | .missingRank a =>
      { layer := "taxon", code := "missing-rank", severity := .warning,
        status := .suggestedFix, subject := qidText a, object := "", extra := "",
        message := "a declared taxon carries no `taxon rank`",
        fix := "add the `taxon rank` (P105) statement" }

/-- A row of the kinship report. -/
def rowOfKinIssue : KinIssue → Row
  | .danglingFather a b =>
      { layer := "kinship", code := "dangling-father", severity := .error,
        status := .suggestedFix, subject := qidText a, object := qidText b, extra := "",
        message := "`father` (P22) statement with an undeclared endpoint",
        fix := "declare the missing person, or delete the statement" }
  | .danglingMother a b =>
      { layer := "kinship", code := "dangling-mother", severity := .error,
        status := .suggestedFix, subject := qidText a, object := qidText b, extra := "",
        message := "`mother` (P25) statement with an undeclared endpoint",
        fix := "declare the missing person, or delete the statement" }
  | .danglingSpouse a b =>
      { layer := "kinship", code := "dangling-spouse", severity := .error,
        status := .suggestedFix, subject := qidText a, object := qidText b, extra := "",
        message := "`spouse` (P26) statement with an undeclared endpoint",
        fix := "declare the missing person, or delete the statement" }
  | .twoFathers a b c =>
      { layer := "kinship", code := "two-fathers", severity := .error,
        status := .needsReview, subject := qidText a, object := qidText b, extra := qidText c,
        message := "a person is recorded with two different genetic fathers",
        fix := "keep the sourced statement and deprecate the other, or use `stepfather`" }
  | .twoMothers a b c =>
      { layer := "kinship", code := "two-mothers", severity := .error,
        status := .needsReview, subject := qidText a, object := qidText b, extra := qidText c,
        message := "a person is recorded with two different genetic mothers",
        fix := "keep the sourced statement and deprecate the other, or use `stepmother`" }
  | .ancestryCycle a b =>
      { layer := "kinship", code := "ancestry-cycle", severity := .error,
        status := .needsReview, subject := qidText a, object := qidText b, extra := "",
        message := "two distinct people each descend from the other",
        fix := "one of the parenthood statements is wrong; the dates usually say which" }
  | .selfSpouse a =>
      { layer := "kinship", code := "self-spouse", severity := .error,
        status := .suggestedFix, subject := qidText a, object := "", extra := "",
        message := "a person is recorded as their own spouse",
        fix := "delete the `spouse` statement" }
  | .kinClassConfusion a b =>
      { layer := "kinship", code := "kin-class-confusion", severity := .error,
        status := .suggestedFix, subject := qidText a, object := qidText b, extra := "",
        message := "parenthood between items already related by `subclass of` or `instance of`",
        fix := "delete the parenthood statement: the relation is taxonomic" }

/-- A row of the parenting report. -/
def rowOfParentIssue : ParentIssue → Row
  | .danglingParent c pa =>
      { layer := "parenting", code := "dangling-parenthood", severity := .error,
        status := .suggestedFix, subject := qidText c, object := qidText pa, extra := "",
        message := "parenthood statement with an undeclared endpoint",
        fix := "declare the missing person, or delete the statement" }
  | .danglingSpouse a b =>
      { layer := "parenting", code := "dangling-spouse", severity := .error,
        status := .suggestedFix, subject := qidText a, object := qidText b, extra := "",
        message := "`spouse` (P26) statement with an undeclared endpoint",
        fix := "declare the missing person, or delete the statement" }
  | .selfParent a =>
      { layer := "parenting", code := "self-parent", severity := .error,
        status := .suggestedFix, subject := qidText a, object := "", extra := "",
        message := "a person is recorded as their own parent",
        fix := "delete the parenthood statement" }
  | .untypedGeneticParent c pa =>
      { layer := "parenting", code := "untyped-genetic-parent", severity := .error,
        status := .suggestedFix, subject := qidText c, object := qidText pa, extra := "",
        message := "a genetic parent filed under the neutral `parent` (P8810)",
        fix := "restate as `father` (P22) or `mother` (P25)" }
  | .twoGeneticParents c x y =>
      { layer := "parenting", code := "two-genetic-parents", severity := .error,
        status := .needsReview, subject := qidText c, object := qidText x, extra := qidText y,
        message := "a person is recorded with two different genetic parents in one slot",
        fix := "keep the sourced statement and deprecate the other, or use a step relation" }
  | .ancestryCycle a b =>
      { layer := "parenting", code := "ancestry-cycle", severity := .error,
        status := .needsReview, subject := qidText a, object := qidText b, extra := "",
        message := "two distinct people each descend from the other",
        fix := "one of the parenthood statements is wrong; the dates usually say which" }
  | .selfSpouse a =>
      { layer := "parenting", code := "self-spouse", severity := .error,
        status := .suggestedFix, subject := qidText a, object := "", extra := "",
        message := "a person is recorded as their own spouse",
        fix := "delete the `spouse` statement" }
  | .parentClassConfusion c pa =>
      { layer := "parenting", code := "parent-class-confusion", severity := .error,
        status := .suggestedFix, subject := qidText c, object := qidText pa, extra := "",
        message := "parenthood between items already related by `subclass of` or `instance of`",
        fix := "delete the parenthood statement: the relation is taxonomic" }
  | .unsupportedStepparent c pa =>
      { layer := "parenting", code := "unsupported-stepparent", severity := .warning,
        status := .suggestedFix, subject := qidText c, object := qidText pa, extra := "",
        message := "a stepparent who is not the spouse of a parent of the child",
        fix := "add the missing `spouse` statement, or drop the step relation" }

/-! ## The tables -/

/-- The report table of a knowledge base: its errors, then its style warnings. -/
def KB.rows (kb : Wikidata.KB) : List Row :=
  kb.errors.map rowOfIssue ++ kb.warnings.map rowOfIssue

/-- The report table of a series layer, on top of the ontology rows. -/
def SKB.rows (s : Wikidata.SKB) : List Row :=
  KB.rows s.base ++ s.sErrors.map rowOfSeriesIssue ++ s.sWarnings.map rowOfSeriesIssue

/-- The report table of a taxon layer, on top of the ontology rows. -/
def TKB.rows (k : Wikidata.TKB) : List Row :=
  KB.rows k.base ++ k.tErrors.map rowOfTaxonIssue ++ k.tWarnings.map rowOfTaxonIssue

/-- The report table of a kinship layer, on top of the ontology rows. -/
def FKB.rows (f : Wikidata.FKB) : List Row :=
  KB.rows f.base ++ f.fErrors.map rowOfKinIssue

/-- The report table of a parenting layer, on top of the ontology rows. -/
def ParentingKB.rows (k : Wikidata.ParentingKB) : List Row :=
  KB.rows k.base ++ k.pErrors.map rowOfParentIssue ++ k.stepWarnings.map rowOfParentIssue

/-! ### A base with no series statements has nothing to report about its series -/

theorem preds_eq_empty_of_no_follows {s : Wikidata.SKB} (h : s.follows = []) (q : Qid) :
    s.preds q = ∅ := by
  simp [Wikidata.SKB.preds, Wikidata.SKB.predsL, h]

theorem isAfterB_of_no_follows {s : Wikidata.SKB} (h : s.follows = []) (a b : Qid) :
    s.isAfterB a b = decide (b = a) := by
  simp [Wikidata.SKB.isAfterB, Wikidata.SKB.predClosure,
    Reach.reach_eq_singleton_of_succ_empty _ _ (preds_eq_empty_of_no_follows h a)]

/-- On a base with no `follows` statements the series report is empty, so nothing
is lost by not computing it. -/
theorem sErrors_eq_nil_of_no_series {s : Wikidata.SKB} (h1 : s.series = [])
    (h2 : s.follows = []) (h3 : s.ordinals = []) : s.sErrors = [] ∧ s.sWarnings = [] := by
  have hcyc : s.seriesCycleIssues = [] := by
    rw [Wikidata.SKB.seriesCycleIssues, List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro p _
    by_cases hp : p.1 = p.2
    · simp [hp]
    · simp [isAfterB_of_no_follows h2, Ne.symm hp]
  refine ⟨?_, ?_⟩
  · simp [Wikidata.SKB.sErrors, Wikidata.SKB.danglingSeriesIssues,
      Wikidata.SKB.danglingFollowsIssues, Wikidata.SKB.danglingOrdinalIssues,
      Wikidata.SKB.selfFollowsIssues, Wikidata.SKB.forkIssues,
      Wikidata.SKB.seriesMismatchIssues, Wikidata.SKB.taxonomicFollowsIssues,
      h1, h2, h3, hcyc]
  · simp [Wikidata.SKB.sWarnings, Wikidata.SKB.ordinalIssues, h2]

/-- **A base with no series layer reports exactly as a bare knowledge base.** -/
theorem SKB.rows_eq_of_no_series {s : Wikidata.SKB} (h1 : s.series = [])
    (h2 : s.follows = []) (h3 : s.ordinals = []) : SKB.rows s = KB.rows s.base := by
  obtain ⟨he, hw⟩ := sErrors_eq_nil_of_no_series h1 h2 h3
  simp [SKB.rows, he, hw]

/-! ### The table is a faithful copy of the diagnostics -/

/-- **An empty error table certifies the base**: the exported error rows are empty
exactly when the knowledge base is valid. -/
theorem errorRows_eq_nil_iff_valid (kb : Wikidata.KB) :
    kb.errors.map rowOfIssue = [] ↔ kb.valid = true := by
  rw [List.map_eq_nil_iff, Wikidata.KB.errors_eq_nil_iff_valid]

/-- The whole table is empty exactly when the base is clean: valid, and with no
redundant `subclass of` statement. -/
theorem rows_eq_nil_iff_clean (kb : Wikidata.KB) : KB.rows kb = [] ↔ kb.clean = true := by
  simp only [KB.rows, List.append_eq_nil_iff, List.map_eq_nil_iff, Wikidata.KB.clean,
    Bool.and_eq_true, List.isEmpty_iff]

/-- The table has exactly one row per issue. -/
theorem rows_length (kb : Wikidata.KB) :
    (KB.rows kb).length = kb.errors.length + kb.warnings.length := by
  simp [KB.rows]

theorem severity_of_mem_errors {kb : Wikidata.KB} {i : Issue} (h : i ∈ kb.errors) :
    (rowOfIssue i).severity = .error := by
  simp only [Wikidata.KB.errors, List.mem_append, Wikidata.KB.danglingSubIssues,
    Wikidata.KB.danglingInstIssues, Wikidata.KB.danglingDisjIssues, Wikidata.KB.levelInstIssues,
    Wikidata.KB.levelSubIssues, Wikidata.KB.cycleIssues, Wikidata.KB.disjointIssues,
    List.mem_map] at h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h) <;>
    obtain ⟨_, _, rfl⟩ := h <;> rfl

theorem severity_of_mem_warnings {kb : Wikidata.KB} {i : Issue} (h : i ∈ kb.warnings) :
    (rowOfIssue i).severity = .warning := by
  simp only [Wikidata.KB.warnings, List.mem_map] at h
  obtain ⟨_, _, rfl⟩ := h
  rfl

/-- **Nothing is dropped or reclassified**: the table carries exactly one `error`
row per error of the base, and one `warning` row per warning. -/
theorem severity_error_count (kb : Wikidata.KB) :
    ((KB.rows kb).filter (fun r => r.severity == .error)).length = kb.errors.length ∧
    ((KB.rows kb).filter (fun r => r.severity == .warning)).length = kb.warnings.length := by
  have herr : ∀ l : List Issue, (∀ i ∈ l, (rowOfIssue i).severity = .error) →
      ((l.map rowOfIssue).filter (fun r => r.severity == .error)).length = l.length ∧
      ((l.map rowOfIssue).filter (fun r => r.severity == .warning)).length = 0 := by
    intro l hl
    induction l with
    | nil => simp
    | cons i l ih =>
        have hi := hl i List.mem_cons_self
        have ih' := ih fun j hj => hl j (List.mem_cons_of_mem _ hj)
        simp [hi, ih'.1, ih'.2]
  have hwarn : ∀ l : List Issue, (∀ i ∈ l, (rowOfIssue i).severity = .warning) →
      ((l.map rowOfIssue).filter (fun r => r.severity == .error)).length = 0 ∧
      ((l.map rowOfIssue).filter (fun r => r.severity == .warning)).length = l.length := by
    intro l hl
    induction l with
    | nil => simp
    | cons i l ih =>
        have hi := hl i List.mem_cons_self
        have ih' := ih fun j hj => hl j (List.mem_cons_of_mem _ hj)
        simp [hi, ih'.1, ih'.2]
  have h1 := herr kb.errors fun i hi => severity_of_mem_errors hi
  have h2 := hwarn kb.warnings fun i hi => severity_of_mem_warnings hi
  constructor <;> simp [KB.rows, List.filter_append, h1.1, h1.2, h2.1, h2.2]

/-! ### The remediation status is honest -/

/-- Only redundant `subclass of` statements are advertised as having a proved fix. -/
theorem status_provenFix_iff (i : Issue) :
    (rowOfIssue i).status = .provenFix ↔ ∃ a b, i = .redundantSubclass a b := by
  cases i <;> simp [rowOfIssue]

/-- **A `proven-fix` row really can be fixed.**  For every row of the report of a
valid base whose status is `provenFix`, deleting the statement it names keeps the
base valid and changes no derived `subclass of` or `instance of` fact.  This is
`Wikidata.KB.warning_prunable`, read off the report. -/
theorem provenFix_prunable {kb : Wikidata.KB} (hv : kb.valid = true) {r : Row}
    (hr : r ∈ KB.rows kb) (hs : r.status = .provenFix) :
    ∃ a b, r = rowOfIssue (.redundantSubclass a b) ∧
      (kb.dropSub (a, b)).valid = true ∧
      (∀ x y, (kb.dropSub (a, b)).isSubclassOf x y = kb.isSubclassOf x y) ∧
      (∀ x c, (kb.dropSub (a, b)).isInstanceOf x c = kb.isInstanceOf x c) := by
  rw [KB.rows, List.mem_append] at hr
  rcases hr with h | h
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
    obtain ⟨a, b, rfl⟩ := (status_provenFix_iff i).1 hs
    have hsev := severity_of_mem_errors hi
    simp only [rowOfIssue] at hsev
    exact absurd hsev (by decide)
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
    obtain ⟨a, b, rfl⟩ := (status_provenFix_iff i).1 hs
    obtain ⟨h1, h2, h3⟩ := Wikidata.KB.warning_prunable hv hi
    exact ⟨a, b, rfl, h1, h2, h3⟩

/-! ## Counting the error types -/

/-- Every error type the report can produce, in reporting order. -/
def allCodes : List String :=
  ["dangling-sub", "dangling-inst", "dangling-disj", "level-inst", "level-sub",
   "subclass-cycle", "disjoint-violation", "redundant-sub",
   "dangling-series", "dangling-follows", "dangling-ordinal", "self-follows", "series-cycle",
   "forked-series", "series-mismatch", "taxonomic-follows", "ordinal-conflict",
   "dangling-parent-taxon", "dangling-rank", "dangling-taxon-name", "self-parent-taxon",
   "taxon-cycle", "multiple-parent-taxa", "rank-inversion", "duplicate-taxon-name",
   "taxonomic-parent", "missing-rank",
   "dangling-father", "dangling-mother", "two-fathers", "two-mothers", "ancestry-cycle",
   "kin-class-confusion",
   "dangling-parenthood", "dangling-spouse", "self-parent", "untyped-genetic-parent",
   "two-genetic-parents", "self-spouse", "parent-class-confusion", "unsupported-stepparent"]

theorem allCodes_nodup : allCodes.Nodup := by decide

theorem rowOfIssue_code_mem (i : Issue) : (rowOfIssue i).code ∈ allCodes := by
  cases i <;> simp [rowOfIssue, allCodes]

theorem rowOfSeriesIssue_code_mem (i : SeriesIssue) : (rowOfSeriesIssue i).code ∈ allCodes := by
  cases i <;> simp [rowOfSeriesIssue, allCodes]

theorem rowOfTaxonIssue_code_mem (i : TaxonIssue) : (rowOfTaxonIssue i).code ∈ allCodes := by
  cases i <;> simp [rowOfTaxonIssue, allCodes]

theorem rowOfKinIssue_code_mem (i : KinIssue) : (rowOfKinIssue i).code ∈ allCodes := by
  cases i <;> simp [rowOfKinIssue, allCodes]

theorem rowOfParentIssue_code_mem (i : ParentIssue) : (rowOfParentIssue i).code ∈ allCodes := by
  cases i <;> simp [rowOfParentIssue, allCodes]

/-- How many rows report the given error type. -/
def countOf (rows : List Row) (c : String) : ℕ := rows.countP (fun r => r.code == c)

/-- A counting lemma: over a repetition-free list of keys covering everything in
`l`, the counts add up to the length of `l`. -/
theorem count_sum_of_nodup {α : Type} [DecidableEq α] (keys : List α) (hnd : keys.Nodup) :
    ∀ l : List α, (∀ x ∈ l, x ∈ keys) → (keys.map (fun k => l.count k)).sum = l.length := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons x l ih =>
      intro h
      have hx : x ∈ keys := h x List.mem_cons_self
      have hone : ∀ ks : List α, ks.Nodup → x ∈ ks →
          (ks.map (fun k => if x = k then 1 else 0)).sum = 1 := by
        intro ks hks hxk
        induction ks with
        | nil => cases hxk
        | cons k ks ihk =>
            rcases List.mem_cons.1 hxk with rfl | hmem
            · have hnot : ∀ k' ∈ ks, x ≠ k' := by
                intro k' hk' hEq
                exact (List.nodup_cons.1 hks).1 (hEq ▸ hk')
              have : (ks.map (fun k' => if x = k' then 1 else 0)).sum = 0 := by
                refine List.sum_eq_zero ?_
                intro n hn
                obtain ⟨k', hk', rfl⟩ := List.mem_map.1 hn
                simp [hnot k' hk']
              simp [this]
            · have hne : x ≠ k := by
                intro hEq
                exact (List.nodup_cons.1 hks).1 (hEq ▸ hmem)
              simp [hne, ihk (List.nodup_cons.1 hks).2 hmem]
      have hsplit : ∀ k, (x :: l).count k = l.count k + (if x = k then 1 else 0) := by
        intro k
        rw [List.count_cons]
        by_cases hk : x = k <;> simp [hk]
      calc (keys.map (fun k => (x :: l).count k)).sum
          = (keys.map (fun k => l.count k + (if x = k then 1 else 0))).sum := by
            simp [hsplit]
        _ = (keys.map (fun k => l.count k)).sum +
              (keys.map (fun k => if x = k then 1 else 0)).sum := by
            induction keys with
            | nil => simp
            | cons k ks ihk => simp [Nat.add_assoc, Nat.add_left_comm]
        _ = l.length + 1 := by
            rw [ih fun y hy => h y (List.mem_cons_of_mem _ hy), hone keys hnd hx]
        _ = (x :: l).length := by simp

/-- **The counts add up**: summed over the error types, the report counts every
row exactly once. -/
theorem countOf_sum (rows : List Row) (h : ∀ r ∈ rows, r.code ∈ allCodes) :
    (allCodes.map (countOf rows)).sum = rows.length := by
  have hmap : ∀ c, countOf rows c = (rows.map Row.code).count c := by
    intro c
    simp [countOf, List.count_eq_countP, List.countP_map, Function.comp_def]
  have hmem : ∀ x ∈ rows.map Row.code, x ∈ allCodes := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    exact h r hr
  calc (allCodes.map (countOf rows)).sum
      = (allCodes.map (fun c => (rows.map Row.code).count c)).sum :=
        congrArg List.sum (List.map_congr_left fun c _ => hmap c)
    _ = (rows.map Row.code).length := count_sum_of_nodup allCodes allCodes_nodup _ hmem
    _ = rows.length := by simp

/-- The codes of an ontology report are among the known error types. -/
theorem KB.rows_code_mem (kb : Wikidata.KB) : ∀ r ∈ KB.rows kb, r.code ∈ allCodes := by
  intro r hr
  rw [KB.rows, List.mem_append] at hr
  rcases hr with h | h <;> obtain ⟨i, _, rfl⟩ := List.mem_map.1 h <;> exact rowOfIssue_code_mem i

/-! ## The three files -/

/-- The severity of an error type, as reported for the summary: a type is shown
as a warning only if every row of that type is a warning. -/
def codeSeverity (rows : List Row) (c : String) : Severity :=
  if (rows.filter (fun r => r.code == c)).any (fun r => r.severity == .error) then
    .error
  else
    .warning

/-- The status attached to an error type in the summary: the status of the first
row of that type. -/
def codeStatus (rows : List Row) (c : String) : Status :=
  match rows.filter (fun r => r.code == c) with
  | [] => .suggestedFix
  | r :: _ => r.status

/-- The error types that actually occur, with their counts. -/
def summary (rows : List Row) : List (String × ℕ) :=
  (allCodes.map fun c => (c, countOf rows c)).filter fun p => 0 < p.2

/-- The summary as a table: error type, severity, status, count. -/
def summaryFields (rows : List Row) : List (List String) :=
  (summary rows).map fun p =>
    [p.1, (codeSeverity rows p.1).text, (codeStatus rows p.1).text, num p.2]

/-- The column headings of the summary table. -/
def summaryHeader : List String := ["code", "severity", "status", "count"]

/-- The bars of the chart: one per error type that occurs, coloured by severity. -/
def bars (rows : List Row) : List Bar :=
  (summary rows).map fun p =>
    { label := p.1, count := p.2, colour := (codeSeverity rows p.1).colour }

/-- **The chart counts every issue exactly once**: the bars add up to the number
of rows. -/
theorem bars_count_sum (rows : List Row) (h : ∀ r ∈ rows, r.code ∈ allCodes) :
    ((bars rows).map Bar.count).sum = rows.length := by
  have hzero : ∀ l : List String,
      ((((l.map fun c => (c, countOf rows c)).filter fun p => 0 < p.2)).map Prod.snd).sum =
        (l.map (countOf rows)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons c l ih =>
        by_cases hc : 0 < countOf rows c
        · simp [hc, ih]
        · simp [ih, Nat.eq_zero_of_not_pos hc]
  calc ((bars rows).map Bar.count).sum
      = (((summary rows)).map Prod.snd).sum := by
        simp [bars, Function.comp_def]
    _ = (allCodes.map (countOf rows)).sum := hzero allCodes
    _ = rows.length := countOf_sum rows h

/-- The report of a table as a CSV file. -/
def csvOfRows (rows : List Row) : String :=
  csvText header (rows.map Row.fields)

theorem Row.fields_ne_nil (r : Row) : r.fields ≠ [] := by simp [Row.fields]

/-- **A report file reads back exactly**: parsing the CSV a report was written to
returns the header and then the fields of each row, in order.  The hypothesis
holds of every report the library produces: its fields are identifiers and fixed
phrases. -/
theorem parseCsvText_csvOfRows {rows : List Row}
    (h : ∀ r ∈ rows, ∀ f ∈ r.fields, '\n' ∉ f.toList) :
    parseCsvText (csvOfRows rows) = some (header :: rows.map Row.fields) := by
  refine parseCsvText_csvText (by simp [header]) (by decide) ?_
  intro fs hfs
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hfs
  exact ⟨Row.fields_ne_nil r, h r hr⟩

/-- The report of a table as an HTML page. -/
def htmlOfRows (title : String) (intro : String) (rows : List Row) : String :=
  htmlText title intro header
    ((summaryFields rows).map fun fs =>
      (fs[1]?.getD "error", fs))
    summaryHeader
    (rows.map fun r => (r.severity.text, r.fields))

/-- The report of a table as an SVG bar chart. -/
def svgOfRows (title : String) (subtitle : String) (rows : List Row) : String :=
  svgText title subtitle (bars rows)

end Report
end Wikidata
