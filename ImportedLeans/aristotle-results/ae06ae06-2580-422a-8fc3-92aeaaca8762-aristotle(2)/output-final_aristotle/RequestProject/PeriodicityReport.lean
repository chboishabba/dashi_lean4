import RequestProject.Periodicity
import RequestProject.KbTerms

/-!
# The periodicity search, applied to the downloaded corpus

`RequestProject.Periodicity` develops the search for periodic points of a graph;
this module runs it over the whole of the downloaded Wikidata data — the 1578
items and 2257 `subclass of` statements of `DefectReport.corpus` — and names
every item it finds with the terms downloaded in `RequestProject.KbTerms`.
Every number below is decided by computation on the data.

* `periodicItems_eq`, `periodicItems_count` — **eleven items of the corpus are
  periodic points of the class hierarchy**, and they are exactly the items the
  cycle detection of the defect report finds (`mem_periodicItems_iff`, using
  that the corpus has no `subclass of` self-loop); the other 1567 are aperiodic
  (`aperiodicItems_count`);
* `periodicItems_labels` — what those items are called, straight from the term
  table: *geographical area*, *academic professional*, *academic*, *region*,
  *scientist*, *researcher*, *delict*, *violation of law*, *element*, *element
  of set*, *element*.  Two of the eleven carry the *same label*, which is what
  the duplication looks like from the term side
  (`RequestProject.KbTerms.element_byLabel`);
* `periods` — the length of the shortest cycle through each of them: 2, 4, 3
  and 2 for the four components;
* for each of the four components a **phase certificate** proves that *every*
  cycle through the component has length divisible by that number, so the return
  times of, say, *scientist* are exactly the positive multiples of four
  (`scientist_returns`).  The period of each component is therefore known
  exactly, not just bounded;
* `acyclicCorpus_no_periodic` — the four deletions that break the cycles in the
  defect report leave a hierarchy with **no periodic point at all**.

The closure of a corpus this size is expensive, so everything that needs it is
decided in the single computation `corpus_scan`, against the one table
`corpusTable`.
-/

namespace Wikidata
namespace PeriodicityReport

open Wikidata.Generated Wikidata.Periodicity Wikidata.DefectReport

/-! ### The phases of the four components

For each component a *phase* assigns to its items consecutive residues, so that
every `subclass of` step inside the component advances the phase by one.  The
check `KB.phaseOkBT` verifies this against the corpus, and
`KB.isPeriodDivisor_of_phaseOkB` turns it into the statement that the length of
*every* cycle through the component is divisible by the phase modulus. -/

/-- *region* (Q82794) and *geographical area* (Q3622002). -/
def regionPhase : Qid → ZMod 2 := fun q => if q = Qid.wd "Q82794" then 0 else 1

/-- *scientist* (Q901) ⊑ *researcher* (Q1650915) ⊑ *academic professional*
(Q66666685) ⊑ *academic* (Q3400985) ⊑ *scientist*. -/
def scientistPhase : Qid → ZMod 4 := fun q =>
  if q = Qid.wd "Q901" then 0
  else if q = Qid.wd "Q1650915" then 1
  else if q = Qid.wd "Q66666685" then 2
  else 3

/-- *element* (Q379825) ⊑ *element* (Q5358816) ⊑ *element of set* (Q36808958) ⊑
*element*. -/
def elementPhase : Qid → ZMod 3 := fun q =>
  if q = Qid.wd "Q379825" then 0
  else if q = Qid.wd "Q5358816" then 1
  else 2

/-- *delict* (Q1184244) and *violation of law* (Q1456832). -/
def delictPhase : Qid → ZMod 2 := fun q => if q = Qid.wd "Q1184244" then 0 else 1

/-! ### The scan -/

/-- The closure table of the corpus, computed once for the whole report. -/
def corpusTable : List (Qid × Finset Qid) := corpus.closureTable

/-- **The scan**: the periodic items of the corpus, the number of aperiodic
ones, and the four phase certificates — all decided against one closure
table. -/
theorem corpus_scan :
    corpus.periodicItemsT corpusTable =
        [Qid.wd "Q3622002", Qid.wd "Q66666685", Qid.wd "Q3400985", Qid.wd "Q82794",
         Qid.wd "Q901", Qid.wd "Q1650915", Qid.wd "Q1184244", Qid.wd "Q1456832",
         Qid.wd "Q379825", Qid.wd "Q36808958", Qid.wd "Q5358816"] ∧
      (corpus.aperiodicItemsT corpusTable).length = 1567 ∧
      corpus.phaseOkBT corpusTable (Qid.wd "Q82794") 2 regionPhase = true ∧
      corpus.phaseOkBT corpusTable (Qid.wd "Q901") 4 scientistPhase = true ∧
      corpus.phaseOkBT corpusTable (Qid.wd "Q379825") 3 elementPhase = true ∧
      corpus.phaseOkBT corpusTable (Qid.wd "Q1184244") 2 delictPhase = true := by
  native_decide

/-! ### What the search finds -/

/-- The eleven items found, in the order the corpus lists them. -/
theorem periodicItems_eq :
    corpus.periodicItems =
      [Qid.wd "Q3622002", Qid.wd "Q66666685", Qid.wd "Q3400985", Qid.wd "Q82794",
       Qid.wd "Q901", Qid.wd "Q1650915", Qid.wd "Q1184244", Qid.wd "Q1456832",
       Qid.wd "Q379825", Qid.wd "Q36808958", Qid.wd "Q5358816"] :=
  corpus_scan.1

/-- **Eleven items of the corpus lie on a `subclass of` cycle.** -/
theorem periodicItems_count : corpus.periodicItems.length = 11 := by
  rw [periodicItems_eq]
  rfl

/-- The other 1567 items are aperiodic. -/
theorem aperiodicItems_count : corpus.aperiodicItems.length = 1567 :=
  corpus_scan.2.1

/-- No `subclass of` statement of the corpus is a self-loop. -/
theorem corpus_no_selfLoopB : corpus.sub.all (fun p => p.1 != p.2) = true := by native_decide

theorem corpus_no_selfLoop (a : Qid) : ¬ corpus.Sub a a := by
  intro h
  have := List.all_eq_true.1 corpus_no_selfLoopB (a, a) h
  simp at this

/-- The periodicity search finds exactly the items the cycle detection of the
defect report finds — and, unlike it, a period for each. -/
theorem mem_periodicItems_iff (x : Qid) : x ∈ corpus.periodicItems ↔ x ∈ corpus.cyclicItems :=
  corpus.mem_periodicItems_iff_mem_cyclicItems corpus_wellFormed corpus_no_selfLoop

/-- Each of them really is a periodic point of the `subclass of` graph. -/
theorem isPeriodic_of_mem_periodicItems {x : Qid} (hx : x ∈ corpus.periodicItems) :
    IsPeriodic corpus.supersL x :=
  (corpus.mem_periodicItems corpus_wellFormed).1 hx

/-! ### The eleven items, their names and their periods -/

/-- What Wikidata calls them, from the downloaded term table. -/
theorem periodicItems_labels :
    [Qid.wd "Q3622002", Qid.wd "Q66666685", Qid.wd "Q3400985", Qid.wd "Q82794",
      Qid.wd "Q901", Qid.wd "Q1650915", Qid.wd "Q1184244", Qid.wd "Q1456832",
      Qid.wd "Q379825", Qid.wd "Q36808958", Qid.wd "Q5358816"].map
        (fun x => kbTerms.labelOf x "en") =
      [some "geographical area", some "academic professional", some "academic",
       some "region", some "scientist", some "researcher", some "delict",
       some "violation of law", some "element", some "element of set",
       some "element"] := by native_decide

/-- The length of the shortest `subclass of` cycle through each of them. -/
theorem periods :
    [Qid.wd "Q3622002", Qid.wd "Q66666685", Qid.wd "Q3400985", Qid.wd "Q82794",
      Qid.wd "Q901", Qid.wd "Q1650915", Qid.wd "Q1184244", Qid.wd "Q1456832",
      Qid.wd "Q379825", Qid.wd "Q36808958", Qid.wd "Q5358816"].map
        (fun x => corpus.subPeriodOf 20 x) =
      [some 2, some 4, some 4, some 2, some 4, some 4, some 2, some 2, some 3,
       some 3, some 3] := by native_decide

/-! ### The four components, with their exact periods -/

theorem region_phaseOk : corpus.phaseOkB (Qid.wd "Q82794") 2 regionPhase = true :=
  corpus_scan.2.2.1

/-- Every `subclass of` cycle through *region* has even length. -/
theorem region_periodDivisor : IsPeriodDivisor corpus.supersL 2 (Qid.wd "Q82794") :=
  corpus.isPeriodDivisor_of_phaseOkB corpus_wellFormed region_phaseOk

theorem region_isReturn_two : IsReturn corpus.supersL 2 (Qid.wd "Q82794") :=
  periodOf_isReturn (by native_decide : corpus.subPeriodOf 20 (Qid.wd "Q82794") = some 2)

/-- **The period of the *region* component is exactly two**: its return times are
the positive even numbers. -/
theorem region_returns (n : ℕ) :
    IsReturn corpus.supersL n (Qid.wd "Q82794") ↔ ∃ k, 0 < k ∧ n = 2 * k :=
  isReturn_iff_multiple region_isReturn_two region_periodDivisor n

theorem scientist_phaseOk : corpus.phaseOkB (Qid.wd "Q901") 4 scientistPhase = true :=
  corpus_scan.2.2.2.1

/-- Every `subclass of` cycle through *scientist* has length divisible by four. -/
theorem scientist_periodDivisor : IsPeriodDivisor corpus.supersL 4 (Qid.wd "Q901") :=
  corpus.isPeriodDivisor_of_phaseOkB corpus_wellFormed scientist_phaseOk

theorem scientist_isReturn_four : IsReturn corpus.supersL 4 (Qid.wd "Q901") :=
  periodOf_isReturn (by native_decide : corpus.subPeriodOf 20 (Qid.wd "Q901") = some 4)

/-- **The period of the *scientist* component is exactly four.** -/
theorem scientist_returns (n : ℕ) :
    IsReturn corpus.supersL n (Qid.wd "Q901") ↔ ∃ k, 0 < k ∧ n = 4 * k :=
  isReturn_iff_multiple scientist_isReturn_four scientist_periodDivisor n

theorem element_phaseOk : corpus.phaseOkB (Qid.wd "Q379825") 3 elementPhase = true :=
  corpus_scan.2.2.2.2.1

/-- Every `subclass of` cycle through *element* has length divisible by three. -/
theorem element_periodDivisor : IsPeriodDivisor corpus.supersL 3 (Qid.wd "Q379825") :=
  corpus.isPeriodDivisor_of_phaseOkB corpus_wellFormed element_phaseOk

theorem element_isReturn_three : IsReturn corpus.supersL 3 (Qid.wd "Q379825") :=
  periodOf_isReturn (by native_decide : corpus.subPeriodOf 20 (Qid.wd "Q379825") = some 3)

/-- **The period of the *element* component is exactly three.** -/
theorem element_returns (n : ℕ) :
    IsReturn corpus.supersL n (Qid.wd "Q379825") ↔ ∃ k, 0 < k ∧ n = 3 * k :=
  isReturn_iff_multiple element_isReturn_three element_periodDivisor n

theorem delict_phaseOk : corpus.phaseOkB (Qid.wd "Q1184244") 2 delictPhase = true :=
  corpus_scan.2.2.2.2.2

/-- Every `subclass of` cycle through *delict* has even length. -/
theorem delict_periodDivisor : IsPeriodDivisor corpus.supersL 2 (Qid.wd "Q1184244") :=
  corpus.isPeriodDivisor_of_phaseOkB corpus_wellFormed delict_phaseOk

theorem delict_isReturn_two : IsReturn corpus.supersL 2 (Qid.wd "Q1184244") :=
  periodOf_isReturn (by native_decide : corpus.subPeriodOf 20 (Qid.wd "Q1184244") = some 2)

/-- **The period of the *delict* component is exactly two.** -/
theorem delict_returns (n : ℕ) :
    IsReturn corpus.supersL n (Qid.wd "Q1184244") ↔ ∃ k, 0 < k ∧ n = 2 * k :=
  isReturn_iff_multiple delict_isReturn_two delict_periodDivisor n

/-! ### The repair removes the periodicity -/

/-- After the four deletions of the defect report the search finds nothing. -/
theorem acyclicCorpus_periodicItems : acyclicCorpus.periodicItems = [] := by native_decide

/-- **No item of the repaired hierarchy is a periodic point.** -/
theorem acyclicCorpus_no_periodic (x : Qid) : ¬ IsPeriodic acyclicCorpus.supersL x := by
  intro h
  have := (acyclicCorpus.mem_periodicItems acyclicCorpus_wellFormed).2 h
  rw [acyclicCorpus_periodicItems] at this
  exact absurd this (by simp)

end PeriodicityReport
end Wikidata
