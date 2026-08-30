import RequestProject.SeriesExamples
import RequestProject.Diagnostics

/-!
# A diagnostic report for the series layer

`RequestProject.Diagnostics` turns the Boolean validator of a knowledge base into a list of
concrete, individually witnessed issues.  This file does the same for the series layer of
`RequestProject.Series`: `follows` (P155) statements pointing at undeclared items, an item
declared to follow itself, a genuine cycle in the series, an item following two different
items (a forking series), neighbours placed in different series, and `follows` statements
between items already related by `subclass of` or `instance of`.

Ordinal problems are reported separately as warnings: `series ordinal` (P1545) values that
disagree with the `follows` statements.

The report is **sound and complete**: it is empty exactly when the layer passes the
validator (`SKB.sErrors_eq_nil_iff`, `SKB.report_eq_nil_iff_sValid`), so nothing is invented
and nothing is missed, and every issue carries its witness.
-/

namespace Wikidata

/-- The kinds of problem a series layer can have. -/
inductive SeriesIssue where
  /-- A `part of the series` (P179) statement with an endpoint that is not a declared item. -/
  | danglingSeries (a t : Qid)
  /-- A `follows` (P155) statement with an endpoint that is not a declared item. -/
  | danglingFollows (a b : Qid)
  /-- A `series ordinal` (P1545) value attached to an item that is not declared. -/
  | danglingOrdinal (a : Qid)
  /-- An item declared to follow itself. -/
  | selfFollows (a : Qid)
  /-- Two distinct items each coming after the other. -/
  | seriesCycle (a b : Qid)
  /-- An item following two different items: the series forks. -/
  | forkedSeries (a b c : Qid)
  /-- Two neighbours in the chain that belong to different series. -/
  | seriesMismatch (a b : Qid)
  /-- A `follows` statement between items already related by `subclass of` or `instance of`. -/
  | taxonomicFollows (a b : Qid)
  /-- `series ordinal` values that do not increase along a `follows` statement. -/
  | ordinalConflict (a b : Qid)
deriving DecidableEq, Repr, Inhabited

namespace SKB

variable (s : SKB)

/-! ### The individual checks -/

/-- P179 statements with an undeclared endpoint. -/
def danglingSeriesIssues : List SeriesIssue :=
  (s.series.filter (fun r => !(r.1 ∈ s.base.items && r.2 ∈ s.base.items))).map
    (fun r => SeriesIssue.danglingSeries r.1 r.2)

/-- P155 statements with an undeclared endpoint. -/
def danglingFollowsIssues : List SeriesIssue :=
  (s.follows.filter (fun r => !(r.1 ∈ s.base.items && r.2 ∈ s.base.items))).map
    (fun r => SeriesIssue.danglingFollows r.1 r.2)

/-- P1545 values attached to undeclared items. -/
def danglingOrdinalIssues : List SeriesIssue :=
  (s.ordinals.filter (fun r => !(r.1 ∈ s.base.items))).map
    (fun r => SeriesIssue.danglingOrdinal r.1)

/-- Items declared to follow themselves. -/
def selfFollowsIssues : List SeriesIssue :=
  (s.follows.filter (fun r => r.1 == r.2)).map (fun r => SeriesIssue.selfFollows r.1)

/-- Genuine cycles in the series. -/
def seriesCycleIssues : List SeriesIssue :=
  ((s.base.items.product s.base.items).filter
    (fun p => s.isAfterB p.1 p.2 && s.isAfterB p.2 p.1 && p.1 != p.2)).map
    (fun p => SeriesIssue.seriesCycle p.1 p.2)

/-- Items following two different items. -/
def forkIssues : List SeriesIssue :=
  ((s.follows.product s.follows).filter (fun p => p.1.1 == p.2.1 && p.1.2 != p.2.2)).map
    (fun p => SeriesIssue.forkedSeries p.1.1 p.1.2 p.2.2)

/-- Neighbours belonging to different series. -/
def seriesMismatchIssues : List SeriesIssue :=
  (s.follows.filter (fun r => s.seriesOfL r.1 != s.seriesOfL r.2)).map
    (fun r => SeriesIssue.seriesMismatch r.1 r.2)

/-- `follows` statements confusing the series with the taxonomy. -/
def taxonomicFollowsIssues : List SeriesIssue :=
  (s.follows.filter (fun r =>
    !(!s.base.isSubclassOf r.1 r.2 && !s.base.isSubclassOf r.2 r.1 &&
      !s.base.isInstanceOf r.1 r.2 && !s.base.isInstanceOf r.2 r.1))).map
    (fun r => SeriesIssue.taxonomicFollows r.1 r.2)

/-- Ordinals disagreeing with the `follows` statements. -/
def ordinalIssues : List SeriesIssue :=
  (s.follows.filter (fun r =>
    !(match s.ordinalOf? r.1, s.ordinalOf? r.2 with
      | some m, some n => decide (n < m)
      | _, _ => true))).map
    (fun r => SeriesIssue.ordinalConflict r.1 r.2)

/-- The full error report of a series layer (the underlying taxonomy is reported
separately, by `KB.errors`). -/
def sErrors : List SeriesIssue :=
  s.danglingSeriesIssues ++ s.danglingFollowsIssues ++ s.danglingOrdinalIssues ++
    s.selfFollowsIssues ++ s.seriesCycleIssues ++ s.forkIssues ++
    s.seriesMismatchIssues ++ s.taxonomicFollowsIssues

/-- The style warnings of a series layer: its ordinal conflicts. -/
def sWarnings : List SeriesIssue := s.ordinalIssues

variable {s}

/-! ### Each check matches its Boolean counterpart -/

theorem danglingSeriesIssues_eq_nil_iff :
    s.danglingSeriesIssues = [] ↔
      s.series.all (fun r => r.1 ∈ s.base.items && r.2 ∈ s.base.items) = true := by
  simp [danglingSeriesIssues, List.filter_eq_nil_iff, List.all_eq_true]

theorem danglingFollowsIssues_eq_nil_iff :
    s.danglingFollowsIssues = [] ↔
      s.follows.all (fun r => r.1 ∈ s.base.items && r.2 ∈ s.base.items) = true := by
  simp [danglingFollowsIssues, List.filter_eq_nil_iff, List.all_eq_true]

theorem danglingOrdinalIssues_eq_nil_iff :
    s.danglingOrdinalIssues = [] ↔ s.ordinals.all (fun r => r.1 ∈ s.base.items) = true := by
  simp [danglingOrdinalIssues, List.filter_eq_nil_iff, List.all_eq_true]

/-- The three dangling checks together are exactly well-formedness of the layer, given a
well-formed taxonomy. -/
theorem sWellFormed_iff (hbase : s.base.wellFormed = true) :
    s.sWellFormed = true ↔
      s.danglingSeriesIssues = [] ∧ s.danglingFollowsIssues = [] ∧
        s.danglingOrdinalIssues = [] := by
  simp only [sWellFormed, Bool.and_eq_true, hbase, true_and,
    danglingSeriesIssues_eq_nil_iff, danglingFollowsIssues_eq_nil_iff,
    danglingOrdinalIssues_eq_nil_iff]
  tauto

theorem selfFollowsIssues_eq_nil_iff :
    s.selfFollowsIssues = [] ↔ s.follows.all (fun r => r.1 != r.2) = true := by
  simp [selfFollowsIssues, List.filter_eq_nil_iff, List.all_eq_true]

theorem seriesCycleIssues_eq_nil_iff :
    s.seriesCycleIssues = [] ↔
      s.base.items.all (fun a => s.base.items.all
        (fun b => !(s.isAfterB a b && s.isAfterB b a) || a == b)) = true := by
  rw [seriesCycleIssues, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  constructor
  · intro h
    simp only [List.all_eq_true]
    intro a ha b hb
    have hp := h (a := (a, b)) (List.pair_mem_product.2 ⟨ha, hb⟩)
    revert hp
    cases hab : s.isAfterB a b <;> cases hba : s.isAfterB b a <;>
      cases heq : (a == b) <;> simp_all
  · rintro h ⟨a, b⟩ hp
    obtain ⟨ha, hb⟩ := List.pair_mem_product.1 hp
    have hall := List.all_eq_true.1 (List.all_eq_true.1 h a ha) b hb
    revert hall
    cases hab : s.isAfterB a b <;> cases hba : s.isAfterB b a <;>
      cases heq : (a == b) <;> simp_all

theorem sAcyclic_iff :
    s.sAcyclic = true ↔ s.selfFollowsIssues = [] ∧ s.seriesCycleIssues = [] := by
  simp only [sAcyclic, Bool.and_eq_true, selfFollowsIssues_eq_nil_iff,
    seriesCycleIssues_eq_nil_iff]

theorem forkIssues_eq_nil_iff : s.forkIssues = [] ↔ s.singlePredecessor = true := by
  rw [forkIssues, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  constructor
  · intro h
    simp only [singlePredecessor, List.all_eq_true]
    rintro r hr r' hr'
    have hp := h (a := (r, r')) (List.pair_mem_product.2 ⟨hr, hr'⟩)
    revert hp
    cases h1 : (r.1 == r'.1) <;> cases h2 : (r.2 == r'.2) <;> simp_all
  · rintro h ⟨r, r'⟩ hp
    obtain ⟨hr, hr'⟩ := List.pair_mem_product.1 hp
    have hall := List.all_eq_true.1 (List.all_eq_true.1 h r hr) r' hr'
    revert hall
    cases h1 : (r.1 == r'.1) <;> cases h2 : (r.2 == r'.2) <;> simp_all

theorem seriesMismatchIssues_eq_nil_iff :
    s.seriesMismatchIssues = [] ↔ s.seriesCoherent = true := by
  simp [seriesMismatchIssues, seriesCoherent, List.filter_eq_nil_iff, List.all_eq_true]

theorem taxonomicFollowsIssues_eq_nil_iff :
    s.taxonomicFollowsIssues = [] ↔ s.noTaxonomyConfusion = true := by
  simp [taxonomicFollowsIssues, noTaxonomyConfusion, List.filter_eq_nil_iff, List.all_eq_true]

theorem ordinalIssues_eq_nil_iff : s.ordinalIssues = [] ↔ s.ordinalsMonotone = true := by
  simp [ordinalIssues, ordinalsMonotone, List.filter_eq_nil_iff, List.all_eq_true]
  exact Iff.rfl

/-! ### The report is sound and complete -/

/-- **The series error report is empty exactly when the series layer passes its checks**
(given a well-formed underlying taxonomy). -/
theorem sErrors_eq_nil_iff (hbase : s.base.wellFormed = true) :
    s.sErrors = [] ↔ s.sLayerValid = true := by
  rw [sErrors]
  simp only [List.append_eq_nil_iff, sLayerValid, Bool.and_eq_true,
    sWellFormed_iff hbase, sAcyclic_iff, forkIssues_eq_nil_iff,
    seriesMismatchIssues_eq_nil_iff, taxonomicFollowsIssues_eq_nil_iff]
  tauto

/-- **The full report**: the taxonomy report and the series report are both empty exactly
when the whole layer is valid. -/
theorem report_eq_nil_iff_sValid :
    (s.base.errors = [] ∧ s.sErrors = []) ↔ s.sValid = true := by
  constructor
  · rintro ⟨hb, hs⟩
    have hvalid : s.base.valid = true := KB.errors_eq_nil_iff_valid.1 hb
    have hwf : s.base.wellFormed = true := KB.valid_wellFormed hvalid
    simp only [sValid, Bool.and_eq_true]
    exact ⟨hvalid, (sErrors_eq_nil_iff hwf).1 hs⟩
  · intro h
    have hvalid : s.base.valid = true := sValid_base h
    have hwf : s.base.wellFormed = true := KB.valid_wellFormed hvalid
    refine ⟨KB.errors_eq_nil_iff_valid.2 hvalid, (sErrors_eq_nil_iff hwf).2 ?_⟩
    simp only [sValid, Bool.and_eq_true] at h
    exact h.2

/-- A series layer with an empty report is one in which every item comes after exactly one
origin: the report being empty is worth something. -/
theorem exists_unique_origin_of_report_eq_nil (hb : s.base.errors = []) (hs : s.sErrors = [])
    (a : Qid) : ∃! b, s.isAfterB a b = true ∧ s.isOriginB b = true :=
  sValid_exists_unique_origin (report_eq_nil_iff_sValid.1 ⟨hb, hs⟩) a

/-! ### The report on the worked examples -/

/-- The worked three-volume series of `RequestProject.Series` reports nothing at all. -/
theorem trilogy_report_clean :
    trilogySKB.base.errors = [] ∧ trilogySKB.sErrors = [] ∧ trilogySKB.sWarnings = [] := by
  decide

/-- A series in which the first volume is also declared to follow the third reports the
cycle, with both witnesses. -/
theorem cyclic_report :
    SeriesIssue.seriesCycle (Qid.wd "v1") (Qid.wd "v3") ∈
      { trilogySKB with
          follows := trilogySKB.follows ++ [(Qid.wd "v1", Qid.wd "v3")] }.sErrors := by
  decide

/-- A forking series reports the fork, naming the two items the volume is said to
follow. -/
theorem forking_report :
    SeriesIssue.forkedSeries (Qid.wd "v3") (Qid.wd "v2") (Qid.wd "v1") ∈
      { trilogySKB with
          follows := trilogySKB.follows ++ [(Qid.wd "v3", Qid.wd "v1")] }.sErrors := by
  decide

/-- Ordinals disagreeing with the `follows` statements are reported as warnings, not as
errors: the ontology is still sound, only its numbering is wrong. -/
theorem bad_ordinals_report :
    { trilogySKB with
        ordinals := [(Qid.wd "v1", 3), (Qid.wd "v2", 2), (Qid.wd "v3", 1)] }.sErrors = [] ∧
    { trilogySKB with
        ordinals := [(Qid.wd "v1", 3), (Qid.wd "v2", 2), (Qid.wd "v3", 1)] }.sWarnings =
      [SeriesIssue.ordinalConflict (Qid.wd "v2") (Qid.wd "v1"),
       SeriesIssue.ordinalConflict (Qid.wd "v3") (Qid.wd "v2")] := by
  decide

end SKB

end Wikidata
