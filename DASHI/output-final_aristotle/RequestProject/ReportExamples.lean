/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.Fixes

/-!
# The report files, checked at compile time

Small worked examples of `RequestProject.Reports` and `RequestProject.ReportFormat`,
all machine-checked:

* the report of the defective base of `RequestProject.Diagnostics` lists exactly the
  expected error types, each with its witnesses and its remediation status;
* the CSV file written from that report reads back as exactly the rows that were
  written, and the bar chart's bars add up to the number of rows;
* the one warning of the healthy-but-redundant base is advertised as a
  `proven-fix`, and applying that fix — deleting the statement — leaves a base
  whose report is empty;
* the repair engine of `RequestProject.Fixes`, run on both bases: what it
  suggests, what it accepts, and what the candidate base looks like.
-/

namespace Wikidata
namespace Report

open Wikidata.KB (brokenKB redundantKB)

/-! ### A defective base -/

/-- Every issue of the broken base of `RequestProject.Diagnostics` appears in the
report, with its error type, severity, status and witnesses. -/
theorem brokenKB_rows :
    KB.rows brokenKB = [
      rowOfIssue (.danglingSub (Qid.wd "Q1") (Qid.wd "Q9")),
      rowOfIssue (.levelMismatchSub (Qid.wd "Q1") (Qid.wd "Q9")),
      rowOfIssue (.subclassCycle (Qid.wd "Q1") (Qid.wd "Q2")),
      rowOfIssue (.subclassCycle (Qid.wd "Q2") (Qid.wd "Q1")),
      rowOfIssue (.disjointViolation (Qid.wd "Q1") (Qid.wd "Q4") (Qid.wd "Q3")),
      rowOfIssue (.redundantSubclass (Qid.wd "Q1") (Qid.wd "Q9"))] := by
  decide

/-- The error types the report names, in reporting order. -/
theorem brokenKB_codes :
    (KB.rows brokenKB).map Row.code =
      ["dangling-sub", "level-sub", "subclass-cycle", "subclass-cycle",
       "disjoint-violation", "redundant-sub"] := by
  decide

/-- Only the redundancy warning is advertised as having a proved fix; every error
of the broken base asks for a declaration or for a human decision. -/
theorem brokenKB_statuses :
    (KB.rows brokenKB).map Row.status =
      [.suggestedFix, .needsReview, .needsReview, .needsReview, .needsReview,
       .provenFix] := by
  decide

/-- The counts drawn in the chart add up to the number of issues. -/
theorem brokenKB_bars_sum :
    ((bars (KB.rows brokenKB)).map Bar.count).sum = (KB.rows brokenKB).length :=
  bars_count_sum _ (KB.rows_code_mem brokenKB)

/-- The chart draws one bar per error type that occurs. -/
theorem brokenKB_bars :
    (bars (KB.rows brokenKB)).map Bar.label =
      ["dangling-sub", "level-sub", "subclass-cycle", "disjoint-violation",
       "redundant-sub"] := by
  decide

set_option maxRecDepth 4000 in
/-- **The CSV file of this report reads back exactly**: the rows that come out of
the parser are the rows that went in. -/
theorem brokenKB_csv_roundTrip :
    parseCsvText (csvOfRows (KB.rows brokenKB)) =
      some (header :: (KB.rows brokenKB).map Row.fields) :=
  parseCsvText_csvOfRows (by decide)

/-! ### A base whose one problem has a proved fix -/

/-- The healthy base with one redundant statement reports exactly one row, a
warning with a proved fix, naming the statement to delete. -/
theorem redundantKB_rows :
    KB.rows redundantKB = [rowOfIssue (.redundantSubclass (Qid.wd "Q5") (Qid.wd "Q35120"))] := by
  decide

theorem redundantKB_row_status :
    ((KB.rows redundantKB).map Row.status) = [Status.provenFix] := by decide

/-- Applying the suggested fix — deleting the statement the row names — empties
the report. -/
theorem redundantKB_fixed_rows :
    KB.rows (redundantKB.dropSub (Qid.wd "Q5", Qid.wd "Q35120")) = [] := by decide

/-- And the fix is a real one: it keeps the base valid and changes no derived
fact.  This is `Wikidata.Report.provenFix_prunable`, read off the report. -/
theorem redundantKB_fix_is_lossless :
    ∃ a b, rowOfIssue (.redundantSubclass (Qid.wd "Q5") (Qid.wd "Q35120")) =
        rowOfIssue (.redundantSubclass a b) ∧
      (redundantKB.dropSub (a, b)).valid = true ∧
      (∀ x y, (redundantKB.dropSub (a, b)).isSubclassOf x y = redundantKB.isSubclassOf x y) ∧
      (∀ x c, (redundantKB.dropSub (a, b)).isInstanceOf x c = redundantKB.isInstanceOf x c) :=
  provenFix_prunable (by decide) (by rw [redundantKB_rows]; exact List.mem_cons_self) rfl

/-! ### The repair engine on these two bases -/

/-- The engine suggests exactly the one deletion the report proves lossless. -/
theorem redundantKB_suggestedFixes :
    redundantKB.suggestedFixes = [FixAction.dropSub (Qid.wd "Q5") (Qid.wd "Q35120")] := by
  decide

/-- It accepts it, and the candidate base is clean. -/
theorem redundantKB_repair_clean : redundantKB.repair.clean = true := by decide

/-- The candidate is the base with that statement gone, and nothing else changed. -/
theorem redundantKB_repair_eq :
    redundantKB.repair = redundantKB.dropSub (Qid.wd "Q5", Qid.wd "Q35120") := by decide

/-- On the base with several problems the engine suggests one declaration, one
deletion, and four requests for review — the cycle, the level mismatch and the
disjointness violation are decisions it refuses to take by itself. -/
theorem brokenKB_suggestedFixes :
    brokenKB.suggestedFixes = [
      FixAction.declareItem (Qid.wd "Q9"),
      FixAction.review "level-sub" "Q1",
      FixAction.review "subclass-cycle" "Q1",
      FixAction.review "subclass-cycle" "Q2",
      FixAction.review "disjoint-violation" "Q3",
      FixAction.dropSub (Qid.wd "Q1") (Qid.wd "Q9")] := by
  decide

/-- Declaring the missing item is accepted — it removes an error — so the
candidate has strictly fewer errors than the base. -/
theorem brokenKB_repair_declares : Qid.wd "Q9" ∈ brokenKB.repair.items := by decide

theorem brokenKB_repair_errors_lt :
    brokenKB.repair.errors.length < brokenKB.errors.length := by decide

/-- And the repair stops there: the base still has the problems only a human can
decide, so the engine leaves them, and says so. -/
theorem brokenKB_repair_not_valid : brokenKB.repair.valid = false := by decide

end Report
end Wikidata
