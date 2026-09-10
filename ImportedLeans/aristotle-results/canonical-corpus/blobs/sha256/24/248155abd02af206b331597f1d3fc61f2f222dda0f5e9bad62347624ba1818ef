import RequestProject.Worklist
import RequestProject.ReportExamples

/-!
# The worklist, checked at compile time

Small worked examples of `RequestProject.Worklist`, on the defective base of
`RequestProject.Diagnostics` whose report is spelled out in
`RequestProject.ReportExamples`:

* grouped by error type, the six issues become five tasks, the two halves of the
  subclass cycle first because that task is the biggest;
* grouped by remediation status, they become three tasks — what needs a human
  decision, what is mechanical, and the one whose fix is proved lossless;
* grouped by layer, one task: every issue of this base is in the ontology layer;
* the sizes add up to six either way, and the only task advertised as safe is the
  redundant-statement one, whose issues all carry a proved fix.
-/

namespace Wikidata
namespace Report

open Wikidata.KB (brokenKB redundantKB)

/-- The rows of the broken base, as the worklist commands see them. -/
private def brokenRows : List Row := KB.rows brokenKB

/-! ### Grouped by error type -/

/-- Five tasks, the subclass cycle first: it is the only error type with two
witnesses. -/
theorem brokenKB_worklist_codes :
    (worklist byCode brokenRows).map Task.key =
      ["subclass-cycle", "dangling-sub", "level-sub", "disjoint-violation",
       "redundant-sub"] := by
  decide

/-- The task sizes, biggest first. -/
theorem brokenKB_worklist_sizes :
    (worklist byCode brokenRows).map Task.size = [2, 1, 1, 1, 1] := by
  decide

/-- The sizes add up to the number of issues — an instance of
`Wikidata.Report.worklist_size_sum`. -/
theorem brokenKB_worklist_size_sum :
    ((worklist byCode brokenRows).map Task.size).sum = brokenRows.length :=
  worklist_size_sum _ _

/-- Only the redundant-statement task is safe to run unattended. -/
theorem brokenKB_worklist_automatic :
    (worklist byCode brokenRows).map Task.automatic =
      [false, false, false, false, true] := by
  decide

/-- What each task takes: the cycle and the disjointness violation are modelling
decisions, the dangling statement is mechanical, the redundancy is proved safe. -/
theorem brokenKB_worklist_advice :
    (worklist byCode brokenRows).map Task.advice =
      ["by hand: every row needs a modelling decision",
       "mechanical: every row has a straightforward suggested edit",
       "by hand: every row needs a modelling decision",
       "by hand: every row needs a modelling decision",
       "safe: every fix is proved to change no derived fact (`wikidata fix`)"] := by
  decide

/-! ### Grouped by kind of work -/

/-- Three tasks: four issues need a human decision, one is mechanical, and one
carries a fix that is proved to change nothing derivable. -/
theorem brokenKB_worklist_statuses :
    (worklist byStatus brokenRows).map (fun t => (t.key, t.size)) =
      [("needs-review", 4), ("suggested-fix", 1), ("proven-fix", 1)] := by
  decide

/-! ### Grouped by layer -/

/-- Every issue of this base is in the ontology layer, so there is one task. -/
theorem brokenKB_worklist_layers :
    (worklist byLayer brokenRows).map (fun t => (t.key, t.size)) =
      [("ontology", 6)] := by
  decide

/-! ### The files -/

/-- The chart drawn for the worklist counts every issue exactly once. -/
theorem brokenKB_taskBars_sum :
    ((taskBars (worklist byCode brokenRows)).map Bar.count).sum = brokenRows.length :=
  taskBars_count_sum _ _

/-- The page lists all six issues, in worklist order. -/
theorem brokenKB_worklistRows_length :
    (worklistRows byCode brokenRows).length = 6 := by
  decide

/-- **A clean base has an empty worklist**: nothing to work on, and that is a
certificate rather than a silence. -/
theorem clean_worklist_eq_nil (kb : Wikidata.KB) (h : kb.clean = true) :
    worklist byCode (KB.rows kb) = [] :=
  (worklist_eq_nil_iff _ _).2 ((rows_eq_nil_iff_clean kb).2 h)

/-- Applying the one proved fix of the redundant base leaves nothing to work
on. -/
theorem prunedKB_worklist_nil :
    worklist byCode (KB.rows (redundantKB.dropSub (Qid.wd "Q5", Qid.wd "Q35120"))) = [] :=
  clean_worklist_eq_nil _ (by decide)

end Report
end Wikidata
