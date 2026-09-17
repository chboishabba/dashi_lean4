/- Attribution: JMD (github.com/meta-introspector) -/
import RequestProject.RepairReview
import RequestProject.SeriesDiagnostics
import RequestProject.Reports

/-!
# The repair workflow for the series layer

`RequestProject.RepairWorkflow` proposes a checked repair for every issue the
*ontology* layer flags.  This file does the same for the series layer of
`RequestProject.Series`: `part of the series` (P179), `follows` (P155) and
`series ordinal` (P1545).

The shape is the same one, so that a reviewer reading a patch review does not
have to know which layer a line came from:

* `Wikidata.SeriesEdit` — the elementary changes a proposal may ask for.
* `Wikidata.SKB.sFlagged`, `sScore` — everything the series diagnostics flag, and
  the repair debt of the layer.
* `Wikidata.SKB.sPlan` — one to three candidate repairs for *every* flagged
  issue (`Wikidata.SKB.sPlan_covers`), each with the reason for it.
* `Wikidata.SKB.sResolvesB` — the check.  A candidate passes only when the issue
  it was raised for is flagged now and gone afterwards, no error and no warning
  appears that the layer or the base underneath did not already carry, and the
  repair debt strictly falls.
* `Wikidata.SKB.sApplyProposals`, `sAutofix` — applying a selection, each
  proposal re-checked as it is applied, so **any** selection is safe.
* `Wikidata.SKB.sReviewItems` — the review, one line per candidate, in the same
  columns as the ontology review (`Wikidata.reviewHeader`).

Nothing here writes anything back: the workflow proposes and a human decides.
-/

namespace Wikidata

open Report (num)
open Cli (qidText)

/-! ## Elementary edits to a series layer -/

/-- An elementary change to a series layer: the vocabulary in which a repair of
the series layer is proposed. -/
inductive SeriesEdit where
  /-- Delete a `part of the series` (P179) statement. -/
  | dropSeries (a t : Qid)
  /-- Delete a `follows` (P155) statement. -/
  | dropFollows (a b : Qid)
  /-- Delete the `series ordinal` (P1545) value of an item. -/
  | dropOrdinal (a : Qid)
  /-- Declare an item the series statements refer to but the base does not list. -/
  | declareItem (q : Qid)
  /-- Record a different `series ordinal` (P1545) value for an item. -/
  | setOrdinal (a : Qid) (n : ℕ)
  /-- Put an item into a series, replacing the series it was in. -/
  | setSeries (a t : Qid)
deriving DecidableEq, Repr, Inhabited

/-- The edit, in one line, as the review table prints it. -/
def SeriesEdit.text : SeriesEdit → String
  | .dropSeries a t => s!"delete `part of the series` {qidText a} → {qidText t}"
  | .dropFollows a b => s!"delete `follows` {qidText a} → {qidText b}"
  | .dropOrdinal a => s!"delete the `series ordinal` of {qidText a}"
  | .declareItem q => s!"declare the item {qidText q}"
  | .setOrdinal a n => s!"set the `series ordinal` of {qidText a} to {n}"
  | .setSeries a t => s!"put {qidText a} in the series {qidText t}"

/-- A list of series edits, in one line. -/
def seriesEditsText : List SeriesEdit → String
  | [] => "(no change)"
  | [e] => e.text
  | e :: es => e.text ++ "; " ++ seriesEditsText es

namespace SKB

/-! ## Applying edits -/

/-- The series layer after one edit. -/
def sEdit (s : SKB) : SeriesEdit → SKB
  | .dropSeries a t => { s with series := s.series.filter (fun r => r != (a, t)) }
  | .dropFollows a b => { s with follows := s.follows.filter (fun r => r != (a, b)) }
  | .dropOrdinal a => { s with ordinals := s.ordinals.filter (fun r => r.1 != a) }
  | .declareItem q =>
      { s with base := if s.base.items.contains q then s.base
                       else { s.base with items := s.base.items ++ [q] } }
  | .setOrdinal a n => { s with ordinals := (a, n) :: s.ordinals.filter (fun r => r.1 != a) }
  | .setSeries a t => { s with series := (a, t) :: s.series.filter (fun r => r.1 != a) }

/-- The series layer after a list of edits, performed in order. -/
def sPatch (s : SKB) (es : List SeriesEdit) : SKB := es.foldl sEdit s

@[simp] theorem sPatch_nil (s : SKB) : s.sPatch [] = s := rfl

theorem sPatch_cons (s : SKB) (e : SeriesEdit) (es : List SeriesEdit) :
    s.sPatch (e :: es) = (s.sEdit e).sPatch es := rfl

/-! ## How much is wrong with a series layer -/

/-- Everything the series diagnostics flag: the errors and the ordinal
warnings. -/
def sFlagged (s : SKB) : List SeriesIssue := s.sErrors ++ s.sWarnings

theorem mem_sFlagged_of_mem_sErrors {s : SKB} {i : SeriesIssue} (h : i ∈ s.sErrors) :
    i ∈ s.sFlagged := List.mem_append_left _ h

theorem mem_sFlagged_of_mem_sWarnings {s : SKB} {i : SeriesIssue} (h : i ∈ s.sWarnings) :
    i ∈ s.sFlagged := List.mem_append_right _ h

/-- The statements of the series layer. -/
def sStatementCount (s : SKB) : ℕ := s.series.length + s.follows.length + s.ordinals.length

/-- **The repair debt of a series layer**, weighted exactly as the one of the
ontology layer: an error costs most, a warning half as much, and every statement
costs one. -/
def sScore (s : SKB) : ℕ :=
  4 * s.sErrors.length + 2 * s.sWarnings.length + s.sStatementCount

/-- The check for *regression*: the candidate carries no series error and no
series warning the layer did not already carry, and no ontology error and no
ontology warning the base underneath did not already carry. -/
def sNoRegressionB (s s' : SKB) : Bool :=
  s'.sErrors.all (fun e => decide (e ∈ s.sErrors)) &&
    s'.sWarnings.all (fun w => decide (w ∈ s.sWarnings)) &&
    KB.noRegressionB s.base s'.base

theorem sErrors_subset_of_sNoRegression {s s' : SKB} (h : sNoRegressionB s s' = true) :
    ∀ e ∈ s'.sErrors, e ∈ s.sErrors := by
  rw [sNoRegressionB, Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true] at h
  intro e he
  simpa using h.1.1 e he

theorem sWarnings_subset_of_sNoRegression {s s' : SKB} (h : sNoRegressionB s s' = true) :
    ∀ w ∈ s'.sWarnings, w ∈ s.sWarnings := by
  rw [sNoRegressionB, Bool.and_eq_true, Bool.and_eq_true] at h
  have h2 := List.all_eq_true.1 h.1.2
  intro w hw
  simpa using h2 w hw

theorem base_noRegression_of_sNoRegression {s s' : SKB} (h : sNoRegressionB s s' = true) :
    KB.noRegressionB s.base s'.base = true := by
  rw [sNoRegressionB, Bool.and_eq_true] at h
  exact h.2

/-- **A valid layer stays valid**: if nothing new is flagged, and the layer was
valid, the candidate is valid too. -/
theorem sValid_of_sNoRegression {s s' : SKB} (h : sNoRegressionB s s' = true)
    (hv : s.sValid = true) : s'.sValid = true := by
  obtain ⟨hb, hs⟩ := report_eq_nil_iff_sValid.2 hv
  refine report_eq_nil_iff_sValid.1 ⟨?_, ?_⟩
  · refine List.eq_nil_iff_forall_not_mem.2 fun e he => ?_
    have := KB.errors_subset_of_noRegression (base_noRegression_of_sNoRegression h) e he
    rw [hb] at this
    exact absurd this List.not_mem_nil
  · refine List.eq_nil_iff_forall_not_mem.2 fun e he => ?_
    have := sErrors_subset_of_sNoRegression h e he
    rw [hs] at this
    exact absurd this List.not_mem_nil

/-! ## Candidate repairs -/

/-- A candidate repair of the series layer: the issue it is raised for, the edits
it makes, and why they are the right ones. -/
structure SeriesProposal where
  /-- The flagged issue this candidate addresses. -/
  issue : SeriesIssue
  /-- The change it proposes. -/
  edits : List SeriesEdit
  /-- Why this change is the right one. -/
  rationale : String
deriving DecidableEq, Repr, Inhabited

/-- The declaration an endpoint calls for, if the base does not list it. -/
def sDeclareMissingE (s : SKB) (q : Qid) : List SeriesEdit :=
  if s.base.items.contains q then [] else [SeriesEdit.declareItem q]

/-- The candidate repairs for one series issue, as a change and a rationale.
There is always at least one candidate. -/
def sRepairPlansOf (s : SKB) : SeriesIssue → List (List SeriesEdit × String)
  | .danglingSeries a t =>
      [ (s.sDeclareMissingE a ++ s.sDeclareMissingE t,
          "the membership looks intended and only its endpoints are undeclared: declare them"),
        ([.dropSeries a t],
          "if the undeclared endpoint is not a real item, the membership is the mistake") ]
  | .danglingFollows a b =>
      [ (s.sDeclareMissingE a ++ s.sDeclareMissingE b,
          "the statement looks intended and only its endpoints are undeclared: declare them"),
        ([.dropFollows a b],
          "if the undeclared endpoint is not a real item, the statement is the mistake") ]
  | .danglingOrdinal a =>
      [ (s.sDeclareMissingE a,
          "the ordinal looks intended and only its item is undeclared: declare it"),
        ([.dropOrdinal a],
          "if the item is not a real one, the ordinal on it is the mistake") ]
  | .selfFollows a =>
      [ ([.dropFollows a a],
          "nothing comes after itself: the statement is a mistake") ]
  | .seriesCycle a b =>
      [ ([.dropFollows a b],
          "a cycle leaves no first element: delete the statement that closes it"),
        ([.dropFollows b a],
          "a cycle leaves no first element: delete the other statement instead"),
        ([.dropFollows a b, .dropFollows b a],
          "if neither item really comes after the other, delete both statements") ]
  | .forkedSeries a b c =>
      [ ([.dropFollows a c],
          "an item has one predecessor: keep the first and drop the second"),
        ([.dropFollows a b],
          "an item has one predecessor: keep the second and drop the first") ]
  | .seriesMismatch a b =>
      (s.seriesOfL b).map (fun t =>
        ([SeriesEdit.setSeries a t],
          "the order is believed and the membership is wrong: put the item in its neighbour's series")) ++
      (s.seriesOfL a).map (fun t =>
        ([SeriesEdit.setSeries b t],
          "the order is believed and the neighbour's membership is wrong: put it in this item's series")) ++
      [ ([SeriesEdit.dropFollows a b],
          "the two really are in different series, so they are not neighbours") ]
  | .taxonomicFollows a b =>
      [ ([.dropFollows a b],
          "the two items are already related by the taxonomy: `follows` is the wrong property here") ]
  | .ordinalConflict a b =>
      (match s.ordinalOf? b with
        | some n =>
            [ ([SeriesEdit.setOrdinal a (n + 1)],
                "the order is believed and the ordinal is wrong: number the item after its predecessor") ]
        | none => []) ++
      [ ([SeriesEdit.dropOrdinal a],
          "the ordinal of the item is the doubtful one: delete it"),
        ([SeriesEdit.dropOrdinal b],
          "the ordinal of the predecessor is the doubtful one: delete it") ]

/-- The candidate repairs for one series issue. -/
def sRepairsOfIssue (s : SKB) (i : SeriesIssue) : List SeriesProposal :=
  (s.sRepairPlansOf i).map fun p => { issue := i, edits := p.1, rationale := p.2 }

theorem sRepairsOfIssue_issue {s : SKB} {i : SeriesIssue} {p : SeriesProposal}
    (h : p ∈ s.sRepairsOfIssue i) : p.issue = i := by
  obtain ⟨q, -, rfl⟩ := List.mem_map.1 h
  rfl

/-- **No flagged series issue is left without a suggestion.** -/
theorem sRepairsOfIssue_ne_nil (s : SKB) (i : SeriesIssue) : s.sRepairsOfIssue i ≠ [] := by
  cases i <;> simp [sRepairsOfIssue, sRepairPlansOf]

theorem exists_sRepairOfIssue (s : SKB) (i : SeriesIssue) :
    ∃ p ∈ s.sRepairsOfIssue i, p.issue = i := by
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ (sRepairsOfIssue_ne_nil s i)
  exact ⟨p, hp, sRepairsOfIssue_issue hp⟩

/-- The whole repair plan of a series layer. -/
def sPlan (s : SKB) : List SeriesProposal := s.sFlagged.flatMap s.sRepairsOfIssue

/-- **Every flagged series issue has a candidate repair in the plan.** -/
theorem sPlan_covers {s : SKB} {i : SeriesIssue} (h : i ∈ s.sFlagged) :
    ∃ p ∈ s.sPlan, p.issue = i := by
  obtain ⟨p, hp, hpi⟩ := exists_sRepairOfIssue s i
  exact ⟨p, List.mem_flatMap.2 ⟨i, h, hp⟩, hpi⟩

/-- **The plan invents nothing**: every candidate addresses an issue the layer
really flags. -/
theorem mem_sPlan_issue {s : SKB} {p : SeriesProposal} (h : p ∈ s.sPlan) :
    p.issue ∈ s.sFlagged := by
  obtain ⟨i, hi, hp⟩ := List.mem_flatMap.1 h
  rw [sRepairsOfIssue_issue hp]
  exact hi

/-! ## The verdict on a candidate -/

/-- The check a candidate repair of the series layer has to pass. -/
def sResolvesB (s : SKB) (p : SeriesProposal) : Bool :=
  decide (p.issue ∈ s.sFlagged) &&
    !decide (p.issue ∈ (s.sPatch p.edits).sFlagged) &&
    sNoRegressionB s (s.sPatch p.edits) &&
    decide ((s.sPatch p.edits).sScore < s.sScore)

/-- The verdict on a candidate repair of the series layer. -/
def sVerdictOf (s : SKB) (p : SeriesProposal) : KB.Verdict :=
  if s.sResolvesB p then .proven else .rejected

@[simp] theorem sVerdictOf_eq_proven_iff {s : SKB} {p : SeriesProposal} :
    s.sVerdictOf p = .proven ↔ s.sResolvesB p = true := by
  by_cases h : s.sResolvesB p <;> simp [sVerdictOf, h]

/-- **A recommended repair addresses an issue the layer really flags.** -/
theorem sIssue_flagged_of_sResolves {s : SKB} {p : SeriesProposal} (h : s.sResolvesB p = true) :
    p.issue ∈ s.sFlagged := by
  rw [sResolvesB, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_iff] at h
  exact h.1.1.1

/-- **The issue a recommended repair was raised for is gone.** -/
theorem sIssue_not_flagged_of_sResolves {s : SKB} {p : SeriesProposal}
    (h : s.sResolvesB p = true) : p.issue ∉ (s.sPatch p.edits).sFlagged := by
  rw [sResolvesB, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not] at h
  exact h.1.1.2

theorem sNoRegression_of_sResolves {s : SKB} {p : SeriesProposal} (h : s.sResolvesB p = true) :
    sNoRegressionB s (s.sPatch p.edits) = true := by
  rw [sResolvesB, Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1.2

/-- **A recommended repair introduces no new series error.** -/
theorem sErrors_subset_of_sResolves {s : SKB} {p : SeriesProposal} (h : s.sResolvesB p = true) :
    ∀ e ∈ (s.sPatch p.edits).sErrors, e ∈ s.sErrors :=
  sErrors_subset_of_sNoRegression (sNoRegression_of_sResolves h)

/-- **A recommended repair introduces no new series warning.** -/
theorem sWarnings_subset_of_sResolves {s : SKB} {p : SeriesProposal} (h : s.sResolvesB p = true) :
    ∀ w ∈ (s.sPatch p.edits).sWarnings, w ∈ s.sWarnings :=
  sWarnings_subset_of_sNoRegression (sNoRegression_of_sResolves h)

/-- **A recommended repair introduces no new error in the ontology underneath.** -/
theorem base_errors_subset_of_sResolves {s : SKB} {p : SeriesProposal}
    (h : s.sResolvesB p = true) :
    ∀ e ∈ (s.sPatch p.edits).base.errors, e ∈ s.base.errors :=
  KB.errors_subset_of_noRegression (base_noRegression_of_sNoRegression
    (sNoRegression_of_sResolves h))

/-- **A recommended repair improves the layer**: its repair debt goes down. -/
theorem sScore_lt_of_sResolves {s : SKB} {p : SeriesProposal} (h : s.sResolvesB p = true) :
    (s.sPatch p.edits).sScore < s.sScore := by
  rw [sResolvesB, Bool.and_eq_true, decide_eq_true_iff] at h
  exact h.2

/-- **A recommended repair keeps a valid layer valid.** -/
theorem sValid_of_sResolves {s : SKB} {p : SeriesProposal} (h : s.sResolvesB p = true)
    (hv : s.sValid = true) : (s.sPatch p.edits).sValid = true :=
  sValid_of_sNoRegression (sNoRegression_of_sResolves h) hv

/-! ## Applying what a reviewer accepts -/

/-- The layer after a reviewer accepts one candidate.  The check is run again at
the moment of application. -/
def sApplyProposal (s : SKB) (p : SeriesProposal) : SKB :=
  if s.sResolvesB p then s.sPatch p.edits else s

/-- **A candidate that fails the check is never performed.** -/
theorem sApplyProposal_of_rejected {s : SKB} {p : SeriesProposal} (h : s.sResolvesB p = false) :
    s.sApplyProposal p = s := by simp [sApplyProposal, h]

theorem sApplyProposal_sScore_le (s : SKB) (p : SeriesProposal) :
    (s.sApplyProposal p).sScore ≤ s.sScore := by
  by_cases h : s.sResolvesB p = true
  · simp only [sApplyProposal, h, if_true]
    exact (sScore_lt_of_sResolves h).le
  · simp [sApplyProposal, h]

theorem sApplyProposal_sErrors_subset (s : SKB) (p : SeriesProposal) :
    ∀ e ∈ (s.sApplyProposal p).sErrors, e ∈ s.sErrors := by
  by_cases h : s.sResolvesB p = true
  · simp only [sApplyProposal, h, if_true]
    exact sErrors_subset_of_sResolves h
  · simp only [Bool.not_eq_true] at h
    simp [sApplyProposal, h]

theorem sApplyProposal_sWarnings_subset (s : SKB) (p : SeriesProposal) :
    ∀ w ∈ (s.sApplyProposal p).sWarnings, w ∈ s.sWarnings := by
  by_cases h : s.sResolvesB p = true
  · simp only [sApplyProposal, h, if_true]
    exact sWarnings_subset_of_sResolves h
  · simp only [Bool.not_eq_true] at h
    simp [sApplyProposal, h]

theorem sApplyProposal_base_errors_subset (s : SKB) (p : SeriesProposal) :
    ∀ e ∈ (s.sApplyProposal p).base.errors, e ∈ s.base.errors := by
  by_cases h : s.sResolvesB p = true
  · simp only [sApplyProposal, h, if_true]
    exact base_errors_subset_of_sResolves h
  · simp only [Bool.not_eq_true] at h
    simp [sApplyProposal, h]

theorem sApplyProposal_sValid {s : SKB} (hv : s.sValid = true) (p : SeriesProposal) :
    (s.sApplyProposal p).sValid = true := by
  by_cases h : s.sResolvesB p = true
  · simp only [sApplyProposal, h, if_true]
    exact sValid_of_sResolves h hv
  · simp only [Bool.not_eq_true] at h
    simpa [sApplyProposal, h] using hv

/-- The layer after a reviewer accepts a selection of candidates. -/
def sApplyProposals (s : SKB) (ps : List SeriesProposal) : SKB := ps.foldl sApplyProposal s

/-- **Accepting nothing changes nothing.** -/
@[simp] theorem sApplyProposals_nil (s : SKB) : s.sApplyProposals [] = s := rfl

theorem sApplyProposals_cons (s : SKB) (p : SeriesProposal) (ps : List SeriesProposal) :
    s.sApplyProposals (p :: ps) = (s.sApplyProposal p).sApplyProposals ps := rfl

/-- **Any selection of candidates leaves a layer that is no worse.** -/
theorem sApplyProposals_sScore_le : ∀ (ps : List SeriesProposal) (s : SKB),
    (s.sApplyProposals ps).sScore ≤ s.sScore
  | [], _ => Nat.le_refl _
  | p :: ps, s => by
      rw [sApplyProposals_cons]
      exact (sApplyProposals_sScore_le ps _).trans (sApplyProposal_sScore_le s p)

/-- **Any selection of candidates introduces no new series error.** -/
theorem sApplyProposals_sErrors_subset : ∀ (ps : List SeriesProposal) (s : SKB),
    ∀ e ∈ (s.sApplyProposals ps).sErrors, e ∈ s.sErrors
  | [], _, _, he => he
  | p :: ps, s, e, he => by
      rw [sApplyProposals_cons] at he
      exact sApplyProposal_sErrors_subset s p e (sApplyProposals_sErrors_subset ps _ e he)

/-- **Any selection of candidates introduces no new series warning.** -/
theorem sApplyProposals_sWarnings_subset : ∀ (ps : List SeriesProposal) (s : SKB),
    ∀ w ∈ (s.sApplyProposals ps).sWarnings, w ∈ s.sWarnings
  | [], _, _, hw => hw
  | p :: ps, s, w, hw => by
      rw [sApplyProposals_cons] at hw
      exact sApplyProposal_sWarnings_subset s p w (sApplyProposals_sWarnings_subset ps _ w hw)

/-- **Any selection of candidates introduces no new error in the ontology
underneath**: repairing the series layer never breaks the taxonomy. -/
theorem sApplyProposals_base_errors_subset : ∀ (ps : List SeriesProposal) (s : SKB),
    ∀ e ∈ (s.sApplyProposals ps).base.errors, e ∈ s.base.errors
  | [], _, _, he => he
  | p :: ps, s, e, he => by
      rw [sApplyProposals_cons] at he
      exact sApplyProposal_base_errors_subset s p e (sApplyProposals_base_errors_subset ps _ e he)

/-- **Any selection of candidates keeps a valid layer valid.** -/
theorem sApplyProposals_sValid : ∀ (ps : List SeriesProposal) {s : SKB}, s.sValid = true →
    (s.sApplyProposals ps).sValid = true
  | [], _, hv => hv
  | p :: ps, s, hv => by
      rw [sApplyProposals_cons]
      exact sApplyProposals_sValid ps (sApplyProposal_sValid hv p)

/-! ## The workflow -/

/-- The candidates of the plan that pass the check. -/
def sAccepted (s : SKB) : List SeriesProposal := s.sPlan.filter (fun p => s.sResolvesB p)

/-- The candidates of the plan that do not pass the check. -/
def sDeferred (s : SKB) : List SeriesProposal := s.sPlan.filter (fun p => !s.sResolvesB p)

/-- **The plan splits into what is recommended and what is deferred.** -/
theorem sAccepted_append_sDeferred_perm (s : SKB) :
    (s.sAccepted ++ s.sDeferred).Perm s.sPlan :=
  List.filter_append_perm _ _

theorem mem_sAccepted_sResolves {s : SKB} {p : SeriesProposal} (h : p ∈ s.sAccepted) :
    s.sResolvesB p = true := by
  simpa using (List.mem_filter.1 h).2

theorem mem_sDeferred_not_sResolves {s : SKB} {p : SeriesProposal} (h : p ∈ s.sDeferred) :
    s.sResolvesB p = false := by
  simpa using (List.mem_filter.1 h).2

/-- **Every flagged series issue is dealt with**: it has a recommended repair, or
a candidate held back for review — never neither. -/
theorem sCoverage {s : SKB} {i : SeriesIssue} (h : i ∈ s.sFlagged) :
    (∃ p ∈ s.sAccepted, p.issue = i) ∨ (∃ p ∈ s.sDeferred, p.issue = i) := by
  obtain ⟨p, hp, hpi⟩ := sPlan_covers h
  by_cases hr : s.sResolvesB p = true
  · exact Or.inl ⟨p, List.mem_filter.2 ⟨hp, by simpa using hr⟩, hpi⟩
  · simp only [Bool.not_eq_true] at hr
    exact Or.inr ⟨p, List.mem_filter.2 ⟨hp, by simp [hr]⟩, hpi⟩

/-- The layer a reviewer would get by accepting everything the workflow
recommends.  It is a *candidate*: the workflow never writes it back. -/
def sAutofix (s : SKB) : SKB := s.sApplyProposals s.sAccepted

theorem sAutofix_sScore_le (s : SKB) : s.sAutofix.sScore ≤ s.sScore :=
  sApplyProposals_sScore_le _ s

theorem sAutofix_sErrors_subset (s : SKB) : ∀ e ∈ s.sAutofix.sErrors, e ∈ s.sErrors :=
  sApplyProposals_sErrors_subset _ s

theorem sAutofix_base_errors_subset (s : SKB) :
    ∀ e ∈ s.sAutofix.base.errors, e ∈ s.base.errors :=
  sApplyProposals_base_errors_subset _ s

theorem sAutofix_sValid {s : SKB} (hv : s.sValid = true) : s.sAutofix.sValid = true :=
  sApplyProposals_sValid _ hv

theorem sAutofix_eq_self_of_sAccepted_nil {s : SKB} (h : s.sAccepted = []) : s.sAutofix = s := by
  rw [sAutofix, h, sApplyProposals_nil]

theorem sPlan_eq_nil_of_sFlagged_nil {s : SKB} (h : s.sFlagged = []) : s.sPlan = [] := by
  rw [sPlan, h]; rfl

/-- **A layer with nothing flagged is a fixed point**: there is nothing to
propose and nothing is touched. -/
theorem sAutofix_eq_self_of_sFlagged_nil {s : SKB} (h : s.sFlagged = []) : s.sAutofix = s := by
  refine sAutofix_eq_self_of_sAccepted_nil ?_
  rw [sAccepted, sPlan_eq_nil_of_sFlagged_nil h]
  rfl

/-- The layer after `n` rounds of the workflow. -/
def sRounds (s : SKB) : ℕ → SKB
  | 0 => s
  | n + 1 => (s.sRounds n).sAutofix

@[simp] theorem sRounds_zero (s : SKB) : s.sRounds 0 = s := rfl

theorem sRounds_succ (s : SKB) (n : ℕ) : s.sRounds (n + 1) = (s.sRounds n).sAutofix := rfl

/-- **More rounds never cost more.** -/
theorem sRounds_sScore_antitone (s : SKB) : ∀ n, (s.sRounds (n + 1)).sScore ≤ (s.sRounds n).sScore
  | _ => sAutofix_sScore_le _

/-- **More rounds never add a series error.** -/
theorem sRounds_sErrors_subset (s : SKB) : ∀ n, ∀ e ∈ (s.sRounds n).sErrors, e ∈ s.sErrors
  | 0, _, he => he
  | n + 1, e, he => sRounds_sErrors_subset s n e (sAutofix_sErrors_subset _ e he)

/-- **The workflow terminates**: once a round changes nothing, no later round
does either. -/
theorem sRounds_stabilises {s : SKB} {n : ℕ} (h : s.sRounds (n + 1) = s.sRounds n) :
    ∀ m, n ≤ m → s.sRounds m = s.sRounds n := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m hm ih => rw [sRounds_succ, ih, ← sRounds_succ, h]

/-! ## The review -/

/-- One reviewable line of the series patch review. -/
structure SeriesReviewItem where
  /-- The candidate repair the line is about. -/
  proposal : SeriesProposal
  /-- What the check said about it. -/
  verdict : KB.Verdict
  /-- The repair debt of the layer as it stands. -/
  scoreBefore : ℕ
  /-- The repair debt the change would leave. -/
  scoreAfter : ℕ
deriving DecidableEq, Repr, Inhabited

/-- The series patch review: one line per candidate repair, none of them
applied. -/
def sReviewItems (s : SKB) : List SeriesReviewItem :=
  s.sPlan.map fun p =>
    { proposal := p, verdict := s.sVerdictOf p,
      scoreBefore := s.sScore, scoreAfter := (s.sPatch p.edits).sScore }

@[simp] theorem sReviewItems_length (s : SKB) : s.sReviewItems.length = s.sPlan.length := by
  simp [sReviewItems]

theorem mem_sReviewItems_iff {s : SKB} {r : SeriesReviewItem} :
    r ∈ s.sReviewItems ↔ ∃ p ∈ s.sPlan, r =
      { proposal := p, verdict := s.sVerdictOf p,
        scoreBefore := s.sScore, scoreAfter := (s.sPatch p.edits).sScore } := by
  simp [sReviewItems, eq_comm]

/-- **The review covers every flagged series issue.** -/
theorem sReviewItems_covers {s : SKB} {i : SeriesIssue} (h : i ∈ s.sFlagged) :
    ∃ r ∈ s.sReviewItems, r.proposal.issue = i := by
  obtain ⟨p, hp, hpi⟩ := sPlan_covers h
  exact ⟨_, mem_sReviewItems_iff.2 ⟨p, hp, rfl⟩, hpi⟩

/-- **The review invents nothing.** -/
theorem sReviewItems_issue_flagged {s : SKB} {r : SeriesReviewItem} (h : r ∈ s.sReviewItems) :
    r.proposal.issue ∈ s.sFlagged := by
  obtain ⟨p, hp, rfl⟩ := mem_sReviewItems_iff.1 h
  exact mem_sPlan_issue hp

/-- **The review is honest**: the numbers and the verdict on a line are the ones
the check computed. -/
theorem sReviewItems_honest {s : SKB} {r : SeriesReviewItem} (h : r ∈ s.sReviewItems) :
    r.verdict = s.sVerdictOf r.proposal ∧ r.scoreBefore = s.sScore ∧
      r.scoreAfter = (s.sPatch r.proposal.edits).sScore := by
  obtain ⟨p, -, rfl⟩ := mem_sReviewItems_iff.1 h
  exact ⟨rfl, rfl, rfl⟩

theorem sReviewItem_proven_iff {s : SKB} {r : SeriesReviewItem} (h : r ∈ s.sReviewItems) :
    r.verdict = .proven ↔ s.sResolvesB r.proposal = true := by
  obtain ⟨p, -, rfl⟩ := mem_sReviewItems_iff.1 h
  exact sVerdictOf_eq_proven_iff

/-- **A recommended line really lowers the repair debt.** -/
theorem sProven_scoreAfter_lt {s : SKB} {r : SeriesReviewItem} (h : r ∈ s.sReviewItems)
    (hp : r.verdict = .proven) : r.scoreAfter < r.scoreBefore := by
  obtain ⟨hv, hb, ha⟩ := sReviewItems_honest h
  rw [ha, hb]
  exact sScore_lt_of_sResolves ((sReviewItem_proven_iff h).1 hp)

/-- **A recommended line really removes its issue and breaks nothing**: neither
in the series layer nor in the ontology underneath. -/
theorem sProven_no_regression {s : SKB} {r : SeriesReviewItem} (h : r ∈ s.sReviewItems)
    (hp : r.verdict = .proven) :
    r.proposal.issue ∉ (s.sPatch r.proposal.edits).sFlagged ∧
      (∀ e ∈ (s.sPatch r.proposal.edits).sErrors, e ∈ s.sErrors) ∧
      (∀ w ∈ (s.sPatch r.proposal.edits).sWarnings, w ∈ s.sWarnings) ∧
      (∀ e ∈ (s.sPatch r.proposal.edits).base.errors, e ∈ s.base.errors) := by
  have hr := (sReviewItem_proven_iff h).1 hp
  exact ⟨sIssue_not_flagged_of_sResolves hr, sErrors_subset_of_sResolves hr,
    sWarnings_subset_of_sResolves hr, base_errors_subset_of_sResolves hr⟩

/-! ### Rendering -/

/-- A review line as a list of fields, in the order of `Wikidata.reviewHeader`. -/
def SeriesReviewItem.fields (r : SeriesReviewItem) : List String :=
  let row := Report.rowOfSeriesIssue r.proposal.issue
  [row.code, row.severity.text, row.subject, row.object, row.extra, row.message,
    seriesEditsText r.proposal.edits, r.proposal.rationale, r.verdict.text,
    num r.scoreBefore, num r.scoreAfter]

theorem SeriesReviewItem.fields_length (r : SeriesReviewItem) :
    r.fields.length = reviewHeader.length := by
  simp [SeriesReviewItem.fields, reviewHeader]

theorem SeriesReviewItem.fields_ne_nil (r : SeriesReviewItem) : r.fields ≠ [] := by
  simp [SeriesReviewItem.fields]

/-- One line of the review, as a sentence for a wiki talk page. -/
def SeriesReviewItem.line (r : SeriesReviewItem) : String :=
  let row := Report.rowOfSeriesIssue r.proposal.issue
  "* " ++ row.code ++ " at " ++ row.subject ++
    (if row.object = "" then "" else " / " ++ row.object) ++
    " — proposed change: " ++ seriesEditsText r.proposal.edits ++
    " — why: " ++ r.proposal.rationale ++
    " — verdict: " ++ r.verdict.text ++
    " (repair debt " ++ num r.scoreBefore ++ " → " ++ num r.scoreAfter ++ ")"

/-- The number of series lines with each verdict. -/
def countSeriesVerdict (items : List SeriesReviewItem) (v : KB.Verdict) : ℕ :=
  items.countP (fun r => r.verdict == v)

/-! ## Both layers at once

A stored base carries an ontology and a series layer, and a reviewer wants one
review of both.  The candidates of the two workflows are simply concatenated:
they are written in the same columns (`Wikidata.reviewHeader`), and the `code`
column says which layer a line came from. -/

/-- The repair debt of a whole stored base: the ontology debt plus the series
debt. -/
def totalScore (s : SKB) : ℕ := s.base.score + s.sScore

/-- Every candidate repair of a stored base, as review lines: the ontology ones
first, then the series ones. -/
def reviewFieldRows (s : SKB) : List (List String) :=
  s.base.reviewItemsFast.map ReviewItem.fields ++ s.sReviewItems.map SeriesReviewItem.fields

/-- The same lines, tagged with the class the HTML page gives them. -/
def reviewHtmlRows (s : SKB) : List (String × List String) :=
  s.base.reviewItemsFast.map
      (fun r => ((match r.verdict with | .proven => "warning" | .rejected => "error"), r.fields)) ++
    s.sReviewItems.map
      (fun r => ((match r.verdict with | .proven => "warning" | .rejected => "error"), r.fields))

/-- The same lines, as sentences for a wiki talk page. -/
def reviewLines (s : SKB) : List String :=
  s.base.reviewItemsFast.map ReviewItem.line ++ s.sReviewItems.map SeriesReviewItem.line

/-- How many candidate repairs a stored base has, over both layers. -/
def reviewCount (s : SKB) : ℕ := s.base.reviewItemsFast.length + s.sReviewItems.length

/-- How many candidate repairs of a stored base carry a given verdict. -/
def reviewVerdictCount (s : SKB) (v : KB.Verdict) : ℕ :=
  countVerdict s.base.reviewItemsFast v + countSeriesVerdict s.sReviewItems v

/-- **The review has exactly one line per candidate**, over both layers. -/
theorem reviewFieldRows_length (s : SKB) :
    s.reviewFieldRows.length = s.base.plan.length + s.sPlan.length := by
  simp [reviewFieldRows]

/-- The candidate a reviewer would get by accepting everything both workflows
recommend: the ontology repairs first, then the series repairs.  It is a
candidate — the workflow never writes it back. -/
def repairedCandidate (s : SKB) : SKB :=
  ({ s with base := s.base.autofix } : SKB).sAutofix

/-- **The candidate base carries no ontology error the stored base did not
already carry**, through both halves of the workflow. -/
theorem repairedCandidate_base_errors_subset (s : SKB) :
    ∀ e ∈ s.repairedCandidate.base.errors, e ∈ s.base.errors := fun e he =>
  KB.autofix_errors_subset s.base e
    (sAutofix_base_errors_subset { s with base := s.base.autofix } e he)

/-- **The candidate layer carries no series error that was left after the
ontology repairs.** -/
theorem repairedCandidate_sErrors_subset (s : SKB) :
    ∀ e ∈ s.repairedCandidate.sErrors, e ∈ ({ s with base := s.base.autofix } : SKB).sErrors :=
  sAutofix_sErrors_subset _

/-- **A stored base with nothing flagged in either layer is a fixed point.** -/
theorem repairedCandidate_eq_self (s : SKB) (hb : s.base.clean = true) (hs : s.sFlagged = []) :
    s.repairedCandidate = s := by
  rw [repairedCandidate, KB.autofix_eq_self_of_clean hb]
  exact sAutofix_eq_self_of_sFlagged_nil hs

/-! ### Computed through the closure tables

The ontology half of the review is quadratic if it is computed from the
definitions, so the tool runs it through the closure tables of
`RequestProject.FastEval`; these are the same numbers. -/

/-- `totalScore`, computed through the closure tables. -/
def totalScoreFast (s : SKB) : ℕ := s.base.scoreFast + s.sScore

@[simp] theorem totalScoreFast_eq (s : SKB) : s.totalScoreFast = s.totalScore := by
  simp [totalScoreFast, totalScore]

/-- `repairedCandidate`, computed through the closure tables. -/
def repairedCandidateFast (s : SKB) : SKB :=
  ({ s with base := s.base.autofixFast } : SKB).sAutofix

@[simp] theorem repairedCandidateFast_eq (s : SKB) :
    s.repairedCandidateFast = s.repairedCandidate := by
  simp [repairedCandidateFast, repairedCandidate]

end SKB
end Wikidata
