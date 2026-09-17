/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.RepairReview

/-!
# The repair workflow, exercised on every kind of flagged issue

`RequestProject.RepairWorkflow` proves *general* statements: whatever a candidate
repair is, if the check accepts it then the issue is gone and nothing else broke.
Those statements are silent about whether the check ever accepts anything, and in
particular about the issue types the old engine could only send to a human —
metaclass level mismatches, class hierarchy cycles, disjointness violations.

This file settles that by example.  There is one small base per issue type, each
carrying exactly the defect its name says, and for each of them it is *computed*
that

* the defect is flagged;
* the workflow proposes a repair for it and the check **recommends** the repair;
* the base the recommendation leads to is valid — and, where the defect was the
  only thing wrong, clean;
* the repair debt strictly drops.

`Wikidata.RepairDemo.brokenKB` then carries all eight defects at once, and the
run over it is checked end to end: every issue type on the table, a
recommendation for each, a valid base after one round, and a fixed point after
two.
-/

namespace Wikidata
namespace RepairDemo

open Wikidata.KB

/-- A Wikidata item, by identifier. -/
def q (n : String) : Qid := .wd n

/-! ## One base per issue type -/

/-- A `subclass of` statement pointing at an item the base does not declare. -/
def danglingSubKB : KB where
  name := "dangling-sub"
  items := [q "Q1"]
  levels := [(q "Q1", 1), (q "Q2", 1)]
  sub := [(q "Q1", q "Q2")]

/-- An `instance of` statement pointing at an item the base does not declare. -/
def danglingInstKB : KB where
  name := "dangling-inst"
  items := [q "Q1"]
  levels := [(q "Q1", 0), (q "Q2", 1)]
  inst := [(q "Q1", q "Q2")]

/-- A disjointness declaration naming an item the base does not declare. -/
def danglingDisjKB : KB where
  name := "dangling-disj"
  items := [q "Q1"]
  levels := [(q "Q1", 1), (q "Q2", 1)]
  disj := [(q "Q1", q "Q2")]

/-- An `instance of` statement whose value does not sit one level up. -/
def levelInstKB : KB where
  name := "level-inst"
  items := [q "Q3", q "Q4"]
  levels := [(q "Q3", 0), (q "Q4", 3)]
  inst := [(q "Q3", q "Q4")]

/-- A `subclass of` statement between two items at different levels. -/
def levelSubKB : KB where
  name := "level-sub"
  items := [q "Q5", q "Q6"]
  levels := [(q "Q5", 1), (q "Q6", 2)]
  sub := [(q "Q5", q "Q6")]

/-- Two classes each declared a subclass of the other. -/
def cycleKB : KB where
  name := "cycle"
  items := [q "Q7", q "Q8"]
  levels := [(q "Q7", 1), (q "Q8", 1)]
  sub := [(q "Q7", q "Q8"), (q "Q8", q "Q7")]

/-- An item instantiating two classes declared disjoint. -/
def disjointKB : KB where
  name := "disjoint"
  items := [q "Q9", q "QA", q "QB"]
  levels := [(q "Q9", 0), (q "QA", 1), (q "QB", 1)]
  inst := [(q "Q9", q "QA"), (q "Q9", q "QB")]
  disj := [(q "QA", q "QB")]

/-- A `subclass of` statement already implied by the others. -/
def redundantKB : KB where
  name := "redundant"
  items := [q "QC", q "QD", q "QE"]
  levels := [(q "QC", 1), (q "QD", 1), (q "QE", 1)]
  sub := [(q "QC", q "QD"), (q "QD", q "QE"), (q "QC", q "QE")]

/-! ## Each defect is flagged, and each gets a recommended repair

The `decide` proofs below are computations the kernel checks: they are the
statement that the workflow really does recommend something for every issue type,
including the three the old engine could only forward to a human. -/

theorem danglingSub_flagged :
    Issue.danglingSub (q "Q1") (q "Q2") ∈ danglingSubKB.flagged := by decide

theorem danglingSub_recommended :
    ∃ p ∈ danglingSubKB.accepted, p.issue = Issue.danglingSub (q "Q1") (q "Q2") := by decide

theorem danglingSub_repaired : danglingSubKB.autofix.clean = true := by decide

theorem danglingSub_improves : danglingSubKB.autofix.score < danglingSubKB.score := by decide

theorem danglingInst_flagged :
    Issue.danglingInst (q "Q1") (q "Q2") ∈ danglingInstKB.flagged := by decide

theorem danglingInst_recommended :
    ∃ p ∈ danglingInstKB.accepted, p.issue = Issue.danglingInst (q "Q1") (q "Q2") := by decide

theorem danglingInst_repaired : danglingInstKB.autofix.clean = true := by decide

theorem danglingDisj_flagged :
    Issue.danglingDisj (q "Q1") (q "Q2") ∈ danglingDisjKB.flagged := by decide

theorem danglingDisj_recommended :
    ∃ p ∈ danglingDisjKB.accepted, p.issue = Issue.danglingDisj (q "Q1") (q "Q2") := by decide

theorem danglingDisj_repaired : danglingDisjKB.autofix.clean = true := by decide

theorem levelInst_flagged :
    Issue.levelMismatchInst (q "Q3") (q "Q4") ∈ levelInstKB.flagged := by decide

theorem levelInst_recommended :
    ∃ p ∈ levelInstKB.accepted, p.issue = Issue.levelMismatchInst (q "Q3") (q "Q4") := by decide

theorem levelInst_repaired : levelInstKB.autofix.clean = true := by decide

/-- The first recommendation for the mis-levelled `instance of` statement is the
level change, not the deletion: the workflow keeps the data where it can. -/
theorem levelInst_first_recommendation :
    levelInstKB.accepted.head?.map KB.Proposal.edits =
      some [Edit.setLevel (q "Q4") 1] := by decide

/-- Not every candidate is recommended: reading the mis-levelled statement as a
`subclass of` statement would leave the level discipline broken, so the check
refuses it and the reviewer is told about it instead. -/
theorem levelInst_instToSub_deferred :
    ∃ p ∈ levelInstKB.deferred, p.edits = [Edit.instToSub (q "Q3") (q "Q4")] := by decide

theorem levelSub_flagged :
    Issue.levelMismatchSub (q "Q5") (q "Q6") ∈ levelSubKB.flagged := by decide

theorem levelSub_recommended :
    ∃ p ∈ levelSubKB.accepted, p.issue = Issue.levelMismatchSub (q "Q5") (q "Q6") := by decide

theorem levelSub_repaired : levelSubKB.autofix.clean = true := by decide

/-- The level clash is repaired by re-levelling, not by deleting the statement. -/
theorem levelSub_first_recommendation :
    levelSubKB.accepted.head?.map KB.Proposal.edits =
      some [Edit.setLevel (q "Q5") 2, Edit.setLevel (q "Q6") 2] := by decide

theorem cycle_flagged :
    Issue.subclassCycle (q "Q7") (q "Q8") ∈ cycleKB.flagged := by decide

theorem cycle_recommended :
    ∃ p ∈ cycleKB.accepted, p.issue = Issue.subclassCycle (q "Q7") (q "Q8") := by decide

theorem cycle_repaired : cycleKB.autofix.clean = true := by decide

/-- One statement of the cycle is deleted, not both: the workflow stops as soon
as the issue is gone. -/
theorem cycle_keeps_one_statement : cycleKB.autofix.sub.length = 1 := by decide

theorem disjoint_flagged :
    Issue.disjointViolation (q "QA") (q "QB") (q "Q9") ∈ disjointKB.flagged := by decide

theorem disjoint_recommended :
    ∃ p ∈ disjointKB.accepted,
      p.issue = Issue.disjointViolation (q "QA") (q "QB") (q "Q9") := by decide

theorem disjoint_repaired : disjointKB.autofix.clean = true := by decide

/-- The disjointness declaration is what goes, and both memberships survive: the
workflow deletes the claim the data refutes, not the data. -/
theorem disjoint_keeps_memberships :
    disjointKB.autofix.inst = disjointKB.inst ∧ disjointKB.autofix.disj = [] := by decide

theorem redundant_flagged :
    Issue.redundantSubclass (q "QC") (q "QE") ∈ redundantKB.flagged := by decide

theorem redundant_recommended :
    ∃ p ∈ redundantKB.accepted,
      p.issue = Issue.redundantSubclass (q "QC") (q "QE") := by decide

theorem redundant_repaired : redundantKB.autofix.clean = true := by decide

/-- Deleting the redundant statement changes no derived fact: `QC` is still a
subclass of `QE`. -/
theorem redundant_keeps_answers :
    redundantKB.autofix.isSubclassOf (q "QC") (q "QE") = true := by decide

/-! ## All eight defects at once -/

/-- A base carrying one of every defect the diagnostics know about. -/
def brokenKB : KB where
  name := "broken"
  items := [q "Q1", q "Q3", q "Q4", q "Q5", q "Q6", q "Q7", q "Q8", q "Q9", q "QA", q "QB",
    q "QC", q "QD", q "QE"]
  levels := [(q "Q1", 1), (q "Q2", 1), (q "Q3", 0), (q "Q4", 3), (q "Q5", 1), (q "Q6", 2),
    (q "Q7", 1), (q "Q8", 1), (q "Q9", 0), (q "QA", 1), (q "QB", 1),
    (q "QC", 1), (q "QD", 1), (q "QE", 1)]
  sub := [(q "Q1", q "Q2"), (q "Q5", q "Q6"), (q "Q7", q "Q8"), (q "Q8", q "Q7"),
    (q "QC", q "QD"), (q "QD", q "QE"), (q "QC", q "QE")]
  inst := [(q "Q1", q "Q2"), (q "Q3", q "Q4"), (q "Q9", q "QA"), (q "Q9", q "QB")]
  disj := [(q "Q1", q "Q2"), (q "QA", q "QB")]

/-- The base is broken in every way the report knows: all eight error types are
flagged at once. -/
theorem brokenKB_all_codes :
    ((Report.KB.rows brokenKB).map Report.Row.code).dedup.length = 8 := by decide

/-- **Every flagged issue has a candidate repair**, here as a computation rather
than as the general theorem `Wikidata.KB.plan_covers`. -/
theorem brokenKB_plan_covers :
    brokenKB.flagged.all (fun i => brokenKB.plan.any (fun p => p.issue == i)) = true := by decide

/-- Nothing in the plan is invented: ten issues, twenty-seven candidates for
them. -/
theorem brokenKB_plan_grounded :
    brokenKB.plan.all (fun p => brokenKB.flagged.contains p.issue) = true := by decide

theorem brokenKB_sizes : (brokenKB.flagged.length, brokenKB.plan.length) = (10, 27) := by decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
/-- **One round of the workflow leaves a clean base** — no error and no redundant
statement — and the repair debt falls from 51 to 9, which is the size of the
repaired base itself. -/
theorem brokenKB_round_clean :
    ((brokenKB.rounds 1).clean, (brokenKB.rounds 1).score, brokenKB.score) = (true, 9, 51) := by
  decide

/-- **The workflow then stops**: every later round leaves the base exactly as the
first round left it.  This one is not a computation: it follows from the base
being clean, by `Wikidata.KB.rounds_stabilises`. -/
theorem brokenKB_fixpoint {n : ℕ} (hn : 1 ≤ n) : brokenKB.rounds n = brokenKB.rounds 1 := by
  refine KB.rounds_stabilises ?_ hn
  have := brokenKB_round_clean
  simpa using congrArg (fun t => t.1) this

/-- The repaired base is valid, so it is a genuine Wikidata ontology. -/
theorem brokenKB_round_valid : (brokenKB.rounds 1).valid = true := by
  have h : (brokenKB.rounds 1).clean = true := by
    simpa using congrArg (fun t => t.1) brokenKB_round_clean
  rw [clean, Bool.and_eq_true, List.isEmpty_iff, List.isEmpty_iff] at h
  exact KB.errors_eq_nil_iff_valid.1 h.1

/-- And the repair debt really did go down. -/
theorem brokenKB_improved : (brokenKB.rounds 1).score < brokenKB.score := by
  have h1 : (brokenKB.rounds 1).score = 9 := by
    simpa using congrArg (fun t => t.2.1) brokenKB_round_clean
  have h2 : brokenKB.score = 51 := by
    simpa using congrArg (fun t => t.2.2) brokenKB_round_clean
  omega

end RepairDemo
end Wikidata
