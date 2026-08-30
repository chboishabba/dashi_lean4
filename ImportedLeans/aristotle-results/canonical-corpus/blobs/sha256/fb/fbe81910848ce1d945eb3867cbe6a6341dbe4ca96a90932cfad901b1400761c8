import RequestProject.TaxaExamples
import RequestProject.Diagnostics

/-!
# A diagnostic report for the taxon layer

`RequestProject.Diagnostics` turns the Boolean validator of a knowledge base into a list of
concrete, individually witnessed issues.  This file does the same for the taxon layer of
`RequestProject.Taxa`: `parent taxon` (P171) statements pointing at undeclared items, a
taxon declared to be its own parent, a genuine cycle in the hierarchy, a taxon with two
different parent taxa, `taxon rank` (P105) values that do not increase along `parent
taxon`, two taxa sharing a `taxon name` (P225), and `parent taxon` statements between items
already related by `subclass of` or `instance of`.

Taxa without a rank are reported separately as warnings: a missing `taxon rank` makes the
hierarchy less informative but not unsound.

The report is **sound and complete**: it is empty exactly when the layer passes the
validator (`TKB.tErrors_eq_nil_iff`, `TKB.report_eq_nil_iff_tValid`), so nothing is invented
and nothing is missed, and every issue carries its witness.
-/

namespace Wikidata

/-- The kinds of problem a taxon layer can have. -/
inductive TaxonIssue where
  /-- A `parent taxon` (P171) statement with an endpoint that is not a declared item. -/
  | danglingParent (a b : Qid)
  /-- A `taxon rank` (P105) value attached to an item that is not declared. -/
  | danglingRank (a : Qid)
  /-- A `taxon name` (P225) value attached to an item that is not declared. -/
  | danglingName (a : Qid)
  /-- A taxon declared to be its own parent taxon. -/
  | selfParent (a : Qid)
  /-- Two distinct taxa each descending from the other. -/
  | taxonCycle (a b : Qid)
  /-- A taxon with two different parent taxa: the hierarchy is not a tree. -/
  | multipleParents (a b c : Qid)
  /-- A `parent taxon` statement along which the `taxon rank` does not increase. -/
  | rankInversion (a b : Qid)
  /-- Two distinct taxa carrying the same scientific name. -/
  | duplicateName (a b : Qid)
  /-- A `parent taxon` statement between items already related by `subclass of` or
  `instance of`. -/
  | taxonomicParent (a b : Qid)
  /-- A declared item carrying no `taxon rank`. -/
  | missingRank (a : Qid)
deriving DecidableEq, Repr, Inhabited

namespace TKB

variable (k : TKB)

/-! ### The individual checks -/

/-- P171 statements with an undeclared endpoint. -/
def danglingParentIssues : List TaxonIssue :=
  (k.parents.filter (fun r => !(r.1 ∈ k.base.items && r.2 ∈ k.base.items))).map
    (fun r => TaxonIssue.danglingParent r.1 r.2)

/-- P105 values attached to undeclared items. -/
def danglingRankIssues : List TaxonIssue :=
  (k.ranks.filter (fun r => !(r.1 ∈ k.base.items))).map (fun r => TaxonIssue.danglingRank r.1)

/-- P225 values attached to undeclared items. -/
def danglingNameIssues : List TaxonIssue :=
  (k.names.filter (fun r => !(r.1 ∈ k.base.items))).map (fun r => TaxonIssue.danglingName r.1)

/-- Taxa declared to be their own parent. -/
def selfParentIssues : List TaxonIssue :=
  (k.parents.filter (fun r => r.1 == r.2)).map (fun r => TaxonIssue.selfParent r.1)

/-- Genuine cycles in the hierarchy. -/
def taxonCycleIssues : List TaxonIssue :=
  ((k.base.items.product k.base.items).filter
    (fun p => k.isDescendantB p.1 p.2 && k.isDescendantB p.2 p.1 && p.1 != p.2)).map
    (fun p => TaxonIssue.taxonCycle p.1 p.2)

/-- Taxa with two different parent taxa. -/
def multipleParentIssues : List TaxonIssue :=
  ((k.parents.product k.parents).filter (fun p => p.1.1 == p.2.1 && p.1.2 != p.2.2)).map
    (fun p => TaxonIssue.multipleParents p.1.1 p.1.2 p.2.2)

/-- `parent taxon` statements along which the rank fails to increase. -/
def rankInversionIssues : List TaxonIssue :=
  (k.parents.filter (fun r =>
    !(match k.rankOf? r.1, k.rankOf? r.2 with
      | some p, some q => decide (p.level < q.level)
      | _, _ => true))).map
    (fun r => TaxonIssue.rankInversion r.1 r.2)

/-- Scientific names shared by two distinct taxa. -/
def duplicateNameIssues : List TaxonIssue :=
  ((k.names.product k.names).filter (fun p => p.1.2 == p.2.2 && p.1.1 != p.2.1)).map
    (fun p => TaxonIssue.duplicateName p.1.1 p.2.1)

/-- `parent taxon` statements confusing the hierarchy with the taxonomy. -/
def taxonomicParentIssues : List TaxonIssue :=
  (k.parents.filter (fun r =>
    !(!k.base.isSubclassOf r.1 r.2 && !k.base.isSubclassOf r.2 r.1 &&
      !k.base.isInstanceOf r.1 r.2 && !k.base.isInstanceOf r.2 r.1))).map
    (fun r => TaxonIssue.taxonomicParent r.1 r.2)

/-- Declared items carrying no `taxon rank`. -/
def missingRankIssues : List TaxonIssue :=
  (k.base.items.filter (fun a => !(k.rankOf? a).isSome)).map TaxonIssue.missingRank

/-- The full error report of a taxon layer (the underlying taxonomy is reported separately,
by `KB.errors`). -/
def tErrors : List TaxonIssue :=
  k.danglingParentIssues ++ k.danglingRankIssues ++ k.danglingNameIssues ++
    k.selfParentIssues ++ k.taxonCycleIssues ++ k.multipleParentIssues ++
    k.rankInversionIssues ++ k.duplicateNameIssues ++ k.taxonomicParentIssues

/-- The style warnings of a taxon layer: the taxa with no `taxon rank`. -/
def tWarnings : List TaxonIssue := k.missingRankIssues

variable {k}

/-! ### Each check matches its Boolean counterpart -/

theorem danglingParentIssues_eq_nil_iff :
    k.danglingParentIssues = [] ↔
      k.parents.all (fun r => r.1 ∈ k.base.items && r.2 ∈ k.base.items) = true := by
  simp [danglingParentIssues, List.filter_eq_nil_iff, List.all_eq_true]

theorem danglingRankIssues_eq_nil_iff :
    k.danglingRankIssues = [] ↔ k.ranks.all (fun r => r.1 ∈ k.base.items) = true := by
  simp [danglingRankIssues, List.filter_eq_nil_iff, List.all_eq_true]

theorem danglingNameIssues_eq_nil_iff :
    k.danglingNameIssues = [] ↔ k.names.all (fun r => r.1 ∈ k.base.items) = true := by
  simp [danglingNameIssues, List.filter_eq_nil_iff, List.all_eq_true]

/-- The three dangling checks together are exactly well-formedness of the layer, given a
well-formed taxonomy. -/
theorem tWellFormed_iff (hbase : k.base.wellFormed = true) :
    k.tWellFormed = true ↔
      k.danglingParentIssues = [] ∧ k.danglingRankIssues = [] ∧ k.danglingNameIssues = [] := by
  simp only [tWellFormed, Bool.and_eq_true, hbase, true_and,
    danglingParentIssues_eq_nil_iff, danglingRankIssues_eq_nil_iff,
    danglingNameIssues_eq_nil_iff]
  tauto

theorem selfParentIssues_eq_nil_iff :
    k.selfParentIssues = [] ↔ k.parents.all (fun r => r.1 != r.2) = true := by
  simp [selfParentIssues, List.filter_eq_nil_iff, List.all_eq_true]

theorem taxonCycleIssues_eq_nil_iff :
    k.taxonCycleIssues = [] ↔
      k.base.items.all (fun a => k.base.items.all
        (fun b => !(k.isDescendantB a b && k.isDescendantB b a) || a == b)) = true := by
  rw [taxonCycleIssues, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  constructor
  · intro h
    simp only [List.all_eq_true]
    intro a ha b hb
    have hp := h (a := (a, b)) (List.pair_mem_product.2 ⟨ha, hb⟩)
    revert hp
    cases hab : k.isDescendantB a b <;> cases hba : k.isDescendantB b a <;>
      cases heq : (a == b) <;> simp_all
  · rintro h ⟨a, b⟩ hp
    obtain ⟨ha, hb⟩ := List.pair_mem_product.1 hp
    have hall := List.all_eq_true.1 (List.all_eq_true.1 h a ha) b hb
    revert hall
    cases hab : k.isDescendantB a b <;> cases hba : k.isDescendantB b a <;>
      cases heq : (a == b) <;> simp_all

theorem tAcyclic_iff :
    k.tAcyclic = true ↔ k.selfParentIssues = [] ∧ k.taxonCycleIssues = [] := by
  simp only [tAcyclic, Bool.and_eq_true, selfParentIssues_eq_nil_iff, taxonCycleIssues_eq_nil_iff]

theorem multipleParentIssues_eq_nil_iff :
    k.multipleParentIssues = [] ↔ k.singleParent = true := by
  rw [multipleParentIssues, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  constructor
  · intro h
    simp only [singleParent, List.all_eq_true]
    rintro r hr r' hr'
    have hp := h (a := (r, r')) (List.pair_mem_product.2 ⟨hr, hr'⟩)
    revert hp
    cases h1 : (r.1 == r'.1) <;> cases h2 : (r.2 == r'.2) <;> simp_all
  · rintro h ⟨r, r'⟩ hp
    obtain ⟨hr, hr'⟩ := List.pair_mem_product.1 hp
    have hall := List.all_eq_true.1 (List.all_eq_true.1 h r hr) r' hr'
    revert hall
    cases h1 : (r.1 == r'.1) <;> cases h2 : (r.2 == r'.2) <;> simp_all

theorem rankInversionIssues_eq_nil_iff :
    k.rankInversionIssues = [] ↔ k.ranksStrict = true := by
  simp [rankInversionIssues, ranksStrict, List.filter_eq_nil_iff, List.all_eq_true]
  exact Iff.rfl

theorem duplicateNameIssues_eq_nil_iff :
    k.duplicateNameIssues = [] ↔ k.namesUnique = true := by
  rw [duplicateNameIssues, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  constructor
  · intro h
    simp only [namesUnique, List.all_eq_true]
    rintro r hr r' hr'
    have hp := h (a := (r, r')) (List.pair_mem_product.2 ⟨hr, hr'⟩)
    revert hp
    cases h1 : (r.2 == r'.2) <;> cases h2 : (r.1 == r'.1) <;> simp_all
  · rintro h ⟨r, r'⟩ hp
    obtain ⟨hr, hr'⟩ := List.pair_mem_product.1 hp
    have hall := List.all_eq_true.1 (List.all_eq_true.1 h r hr) r' hr'
    revert hall
    cases h1 : (r.2 == r'.2) <;> cases h2 : (r.1 == r'.1) <;> simp_all

theorem taxonomicParentIssues_eq_nil_iff :
    k.taxonomicParentIssues = [] ↔ k.noTaxonomyConfusion = true := by
  simp [taxonomicParentIssues, noTaxonomyConfusion, List.filter_eq_nil_iff, List.all_eq_true]

theorem missingRankIssues_eq_nil_iff : k.missingRankIssues = [] ↔ k.ranksTotal = true := by
  simp [missingRankIssues, ranksTotal, List.filter_eq_nil_iff, List.all_eq_true,
    Option.isSome_iff_ne_none]

/-! ### The report is sound and complete -/

/-- **The taxon error report is empty exactly when the taxon layer passes its checks**
(given a well-formed underlying taxonomy). -/
theorem tErrors_eq_nil_iff (hbase : k.base.wellFormed = true) :
    k.tErrors = [] ↔ k.tLayerValid = true := by
  rw [tErrors]
  simp only [List.append_eq_nil_iff, tLayerValid, Bool.and_eq_true,
    tWellFormed_iff hbase, tAcyclic_iff, multipleParentIssues_eq_nil_iff,
    rankInversionIssues_eq_nil_iff, duplicateNameIssues_eq_nil_iff,
    taxonomicParentIssues_eq_nil_iff]
  tauto

/-- **The full report**: the taxonomy report and the taxon report are both empty exactly
when the whole layer is valid. -/
theorem report_eq_nil_iff_tValid :
    (k.base.errors = [] ∧ k.tErrors = []) ↔ k.tValid = true := by
  constructor
  · rintro ⟨hb, ht⟩
    have hvalid : k.base.valid = true := KB.errors_eq_nil_iff_valid.1 hb
    have hwf : k.base.wellFormed = true := KB.valid_wellFormed hvalid
    simp only [tValid, Bool.and_eq_true]
    exact ⟨hvalid, (tErrors_eq_nil_iff hwf).1 ht⟩
  · intro h
    have hvalid : k.base.valid = true := tValid_base h
    have hwf : k.base.wellFormed = true := KB.valid_wellFormed hvalid
    refine ⟨KB.errors_eq_nil_iff_valid.2 hvalid, (tErrors_eq_nil_iff hwf).2 ?_⟩
    simp only [tValid, Bool.and_eq_true] at h
    exact h.2

/-- A taxon layer with an empty report is one in which every taxon descends from exactly
one root: the report being empty is worth something. -/
theorem exists_unique_root_of_report_eq_nil (hb : k.base.errors = []) (ht : k.tErrors = [])
    (a : Qid) : ∃! b, k.isDescendantB a b = true ∧ k.isRootB b = true :=
  tValid_exists_unique_root (report_eq_nil_iff_tValid.1 ⟨hb, ht⟩) a

/-! ### The report on the worked example -/

/-- The worked lineage of `RequestProject.TaxaExamples` reports no errors. -/
theorem life_report_clean : lifeTKB.base.errors = [] ∧ lifeTKB.tErrors = [] := by decide

/-- It does carry one warning: `taxon` (Q16521) is a class of the ontology and has no
`taxon rank`. -/
theorem life_report_warning :
    lifeTKB.tWarnings = [TaxonIssue.missingRank (Qid.wd "Q16521")] := by decide

/-- A cycle is reported, with both taxa named. -/
theorem life_cycle_reported :
    TaxonIssue.taxonCycle (Qid.wd "Q729") (Qid.wd "Q15978631") ∈
      { lifeTKB with
        parents := lifeTKB.parents ++ [(Qid.wd "Q729", Qid.wd "Q15978631")] }.tErrors := by
  decide

/-- A second parent taxon is reported, with both parents named. -/
theorem life_fork_reported :
    TaxonIssue.multipleParents (Qid.wd "Q171283") (Qid.wd "Q7380") (Qid.wd "Q7377") ∈
      { lifeTKB with
        parents := lifeTKB.parents ++ [(Qid.wd "Q171283", Qid.wd "Q7377")] }.tErrors := by
  decide

/-- A rank inversion is reported, with the offending statement named. -/
theorem life_rank_inversion_reported :
    TaxonIssue.rankInversion (Qid.wd "Q171283") (Qid.wd "Q7380") ∈
      { lifeTKB with
        ranks := (Qid.wd "Q171283", TaxonRank.kingdom) :: lifeTKB.ranks }.tErrors := by
  decide

end TKB
end Wikidata
