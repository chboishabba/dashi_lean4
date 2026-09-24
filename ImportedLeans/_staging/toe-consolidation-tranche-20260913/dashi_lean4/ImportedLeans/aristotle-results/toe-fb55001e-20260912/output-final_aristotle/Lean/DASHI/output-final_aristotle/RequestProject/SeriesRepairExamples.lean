import RequestProject.SeriesRepair

/-!
# The series repair workflow, exercised on every kind of flagged issue

`RequestProject.SeriesRepair` proves *general* statements about the repair
workflow of the series layer: whatever a candidate is, if the check accepts it
then the issue it was raised for is gone, nothing new is flagged in either layer,
and the repair debt has fallen.  Those statements are silent about whether the
check ever accepts anything.

This file settles that by example.  There is one small layer per issue type, each
carrying the defect its name says, and for each of them it is *computed* that the
defect is flagged, that the workflow recommends a repair for it, and that the
layer comes out with nothing flagged and a smaller repair debt.  A last layer
carries several defects at once.
-/

namespace Wikidata
namespace SeriesRepairDemo

open Wikidata.SKB

/-- A Wikidata item, by identifier. -/
def q (n : String) : Qid := .wd n

/-! ## One layer per issue type -/

/-- A `part of the series` statement naming an item the base does not declare. -/
def danglingSeriesSKB : SKB where
  base := { name := "dangling-series", items := [q "Q1"], levels := [(q "Q1", 0), (q "Q2", 0)] }
  series := [(q "Q1", q "Q2")]

/-- A `follows` statement pointing at an item the base does not declare. -/
def danglingFollowsSKB : SKB where
  base := { name := "dangling-follows", items := [q "Q1"], levels := [(q "Q1", 0), (q "Q2", 0)] }
  follows := [(q "Q1", q "Q2")]

/-- A `series ordinal` on an item the base does not declare. -/
def danglingOrdinalSKB : SKB where
  base := { name := "dangling-ordinal", items := [q "Q1"], levels := [(q "Q1", 0), (q "Q2", 0)] }
  ordinals := [(q "Q2", 1)]

/-- An item declared to follow itself. -/
def selfFollowsSKB : SKB where
  base := { name := "self-follows", items := [q "Q1"], levels := [(q "Q1", 0)] }
  follows := [(q "Q1", q "Q1")]

/-- Two items each declared to come after the other. -/
def seriesCycleSKB : SKB where
  base := { name := "series-cycle", items := [q "Q1", q "Q2"],
            levels := [(q "Q1", 0), (q "Q2", 0)] }
  follows := [(q "Q1", q "Q2"), (q "Q2", q "Q1")]

/-- An item following two different items: the series forks. -/
def forkedSeriesSKB : SKB where
  base := { name := "forked-series", items := [q "Q1", q "Q2", q "Q3"],
            levels := [(q "Q1", 0), (q "Q2", 0), (q "Q3", 0)] }
  follows := [(q "Q1", q "Q2"), (q "Q1", q "Q3")]

/-- Two neighbours declared to be in different series. -/
def seriesMismatchSKB : SKB where
  base := { name := "series-mismatch", items := [q "Q1", q "Q2", q "QA", q "QB"],
            levels := [(q "Q1", 0), (q "Q2", 0), (q "QA", 0), (q "QB", 0)] }
  series := [(q "Q1", q "QA"), (q "Q2", q "QB")]
  follows := [(q "Q1", q "Q2")]

/-- A `follows` statement between items already related by the taxonomy. -/
def taxonomicFollowsSKB : SKB where
  base := { name := "taxonomic-follows", items := [q "Q1", q "Q2"],
            levels := [(q "Q1", 1), (q "Q2", 1)], sub := [(q "Q1", q "Q2")] }
  follows := [(q "Q1", q "Q2")]

/-- Ordinals that do not increase along the series. -/
def ordinalConflictSKB : SKB where
  base := { name := "ordinal-conflict", items := [q "Q1", q "Q2"],
            levels := [(q "Q1", 0), (q "Q2", 0)] }
  follows := [(q "Q1", q "Q2")]
  ordinals := [(q "Q1", 1), (q "Q2", 5)]

/-! ## Each defect is flagged, and each gets a recommended repair -/

theorem danglingSeries_flagged :
    SeriesIssue.danglingSeries (q "Q1") (q "Q2") ∈ danglingSeriesSKB.sFlagged := by decide

theorem danglingSeries_recommended :
    ∃ p ∈ danglingSeriesSKB.sAccepted,
      p.issue = SeriesIssue.danglingSeries (q "Q1") (q "Q2") := by decide

theorem danglingSeries_repaired : danglingSeriesSKB.sAutofix.sFlagged = [] := by decide

theorem danglingSeries_improves :
    danglingSeriesSKB.sAutofix.sScore < danglingSeriesSKB.sScore := by decide

theorem danglingFollows_flagged :
    SeriesIssue.danglingFollows (q "Q1") (q "Q2") ∈ danglingFollowsSKB.sFlagged := by decide

theorem danglingFollows_recommended :
    ∃ p ∈ danglingFollowsSKB.sAccepted,
      p.issue = SeriesIssue.danglingFollows (q "Q1") (q "Q2") := by decide

theorem danglingFollows_repaired : danglingFollowsSKB.sAutofix.sFlagged = [] := by decide

theorem danglingOrdinal_flagged :
    SeriesIssue.danglingOrdinal (q "Q2") ∈ danglingOrdinalSKB.sFlagged := by decide

theorem danglingOrdinal_recommended :
    ∃ p ∈ danglingOrdinalSKB.sAccepted,
      p.issue = SeriesIssue.danglingOrdinal (q "Q2") := by decide

theorem danglingOrdinal_repaired : danglingOrdinalSKB.sAutofix.sFlagged = [] := by decide

theorem selfFollows_flagged :
    SeriesIssue.selfFollows (q "Q1") ∈ selfFollowsSKB.sFlagged := by decide

theorem selfFollows_recommended :
    ∃ p ∈ selfFollowsSKB.sAccepted, p.issue = SeriesIssue.selfFollows (q "Q1") := by decide

theorem selfFollows_repaired : selfFollowsSKB.sAutofix.sFlagged = [] := by decide

theorem seriesCycle_flagged :
    SeriesIssue.seriesCycle (q "Q1") (q "Q2") ∈ seriesCycleSKB.sFlagged := by decide

theorem seriesCycle_recommended :
    ∃ p ∈ seriesCycleSKB.sAccepted,
      p.issue = SeriesIssue.seriesCycle (q "Q1") (q "Q2") := by decide

theorem seriesCycle_repaired : seriesCycleSKB.sAutofix.sFlagged = [] := by decide

/-- One statement of the cycle is deleted, not both: the workflow stops as soon
as the issue is gone. -/
theorem seriesCycle_keeps_one_statement : seriesCycleSKB.sAutofix.follows.length = 1 := by decide

theorem forkedSeries_flagged :
    SeriesIssue.forkedSeries (q "Q1") (q "Q2") (q "Q3") ∈ forkedSeriesSKB.sFlagged := by decide

theorem forkedSeries_recommended :
    ∃ p ∈ forkedSeriesSKB.sAccepted,
      p.issue = SeriesIssue.forkedSeries (q "Q1") (q "Q2") (q "Q3") := by decide

theorem forkedSeries_repaired : forkedSeriesSKB.sAutofix.sFlagged = [] := by decide

theorem seriesMismatch_flagged :
    SeriesIssue.seriesMismatch (q "Q1") (q "Q2") ∈ seriesMismatchSKB.sFlagged := by decide

theorem seriesMismatch_recommended :
    ∃ p ∈ seriesMismatchSKB.sAccepted,
      p.issue = SeriesIssue.seriesMismatch (q "Q1") (q "Q2") := by decide

theorem seriesMismatch_repaired : seriesMismatchSKB.sAutofix.sFlagged = [] := by decide

theorem taxonomicFollows_flagged :
    SeriesIssue.taxonomicFollows (q "Q1") (q "Q2") ∈ taxonomicFollowsSKB.sFlagged := by decide

theorem taxonomicFollows_recommended :
    ∃ p ∈ taxonomicFollowsSKB.sAccepted,
      p.issue = SeriesIssue.taxonomicFollows (q "Q1") (q "Q2") := by decide

theorem taxonomicFollows_repaired : taxonomicFollowsSKB.sAutofix.sFlagged = [] := by decide

/-- Deleting the `follows` statement leaves the taxonomy alone: what the two
items say about each other is still there. -/
theorem taxonomicFollows_keeps_taxonomy :
    taxonomicFollowsSKB.sAutofix.base.sub = [(q "Q1", q "Q2")] := by decide

theorem ordinalConflict_flagged :
    SeriesIssue.ordinalConflict (q "Q1") (q "Q2") ∈ ordinalConflictSKB.sFlagged := by decide

theorem ordinalConflict_recommended :
    ∃ p ∈ ordinalConflictSKB.sAccepted,
      p.issue = SeriesIssue.ordinalConflict (q "Q1") (q "Q2") := by decide

theorem ordinalConflict_repaired : ordinalConflictSKB.sAutofix.sFlagged = [] := by decide

/-- The conflicting ordinal is corrected, not deleted: the workflow keeps the
data where it can. -/
theorem ordinalConflict_first_recommendation :
    ordinalConflictSKB.sAccepted.head?.map SKB.SeriesProposal.edits =
      some [SeriesEdit.setOrdinal (q "Q1") 6] := by decide

/-! ## A layer carrying several defects at once -/

/-- A series layer with a dangling `follows` statement, a self-follows statement,
a cycle and an ordinal conflict. -/
def brokenSKB : SKB where
  base := { name := "broken-series", items := [q "Q1", q "Q2", q "Q3"],
            levels := [(q "Q1", 0), (q "Q2", 0), (q "Q3", 0), (q "Q9", 0)] }
  follows := [(q "Q1", q "Q9"), (q "Q3", q "Q3"), (q "Q1", q "Q2"), (q "Q2", q "Q1")]
  ordinals := [(q "Q1", 1), (q "Q2", 5)]

/-- Eight defects, seventeen candidate repairs. -/
theorem brokenSKB_sizes : (brokenSKB.sFlagged.length, brokenSKB.sPlan.length) = (8, 17) := by
  decide

/-- Every flagged issue has a candidate in the plan. -/
theorem brokenSKB_plan_covers :
    brokenSKB.sFlagged.all (fun i =>
      decide (∃ p ∈ brokenSKB.sPlan, p.issue = i)) = true := by decide

/-- Every candidate in the plan is a candidate for an issue the layer really
flags. -/
theorem brokenSKB_plan_grounded :
    brokenSKB.sPlan.all (fun p => decide (p.issue ∈ brokenSKB.sFlagged)) = true := by decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- One round of the workflow leaves nothing flagged, at a lower repair debt. -/
theorem brokenSKB_round_clean :
    (brokenSKB.sAutofix.sFlagged, brokenSKB.sAutofix.sScore, brokenSKB.sScore) =
      ([], 4, 36) := by decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 20000 in
/-- And the round after that changes nothing: the workflow has converged. -/
theorem brokenSKB_fixpoint : brokenSKB.sAutofix.sAutofix = brokenSKB.sAutofix := by decide

end SeriesRepairDemo
end Wikidata
