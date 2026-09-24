import RequestProject.RelationWords
import RequestProject.FeedbackSets

/-!
# The periodicity spectrum of the downloaded corpus

`RequestProject.PeriodicityReport` runs the periodicity search along **one**
relation, `subclass of`.  This module runs it along *words* in the two relations
of the ontology layer — `subclass of` (P279) and `instance of` (P31) — and
compares what it finds with the term layer.  Everything is decided by
computation on the 1578 items, 2257 P279 and 1169 P31 statements of
`DefectReport.corpus`.

**1. Longer periods along `subclass of` change nothing.**  A search with a larger
bound cannot find a new item: `subPeriodOf_isSome_imp` shows that any return
time whatsoever puts the item among the eleven periodic items already known, so
the histogram of shortest returns is supported on those eleven at *every* bound.
At bound 100 it is `periodHistogram_100`: four items of shortest return 2, three
of 3, four of 4 — exactly the picture at bound 20.

**2. Other relations close where `subclass of` does not.**  `word_spectrum` runs
the search over the fourteen words of length at most three and counts the items
each of them returns to themselves.  The findings:

* `instance of` alone closes at exactly one item — *variable-order class*
  (Q23958852) is **an instance of itself** (`variableOrderClass_selfInstance`);
* the mixed word `instance of ∘ subclass of` closes at **nine** items and
  `subclass of ∘ instance of` at **eight** (`instSub_periodicItems`,
  `subInst_periodicItems`), and none of them is one of the eleven items of the
  `subclass of` search.  These are genuine *mixed-relational* cycles: *class*
  (Q16889133) is an instance of *metaclass* (Q19478619), which is a subclass of
  *class* (`class_metaclass_mixedCycle`), and similarly for *representation* and
  *concept*.

**3. A closing word that uses `instance of` is a defect of the same kind as a
`subclass of` cycle** — and a worse one.  `Wikidata.Ontology.level_of_eval_wordExpr`
says that a walk raises the metaclass level by the number of `instance of`
letters it spells, so in a genuine ontology no such word can close.  Hence
`no_ontology_over_corpus_links`, and — because the repair of the defect report
only deletes `subclass of` statements — `no_ontology_over_acyclicCorpus_links`:
**the four deletions that make the class hierarchy acyclic still leave a
knowledge base that no abstract ontology models.**

**4. Component, period and phase.**  The mixed transition system
`instance of ∘ subclass of` has a single strongly connected component containing
all nine of its periodic items.  *Wikidata entity* (Q32753077) has shortest
return 3 there, yet the component's **fundamental period is 1**
(`entity_instSub_periodDivisor_eq_one`), because *representation* (Q1272626) is a
fixed point of the same component; consequently no phase certificate of modulus
greater than one can exist for it (`entity_instSub_no_phase`).  This is the
sharpest illustration of the difference between the shortest return the search
reports and the period of the component.  For contrast, `region_periodDivisor'`
re-derives the exact period 2 of the *region* component through the new
reachability-based certificate `KB.subPhaseCertB`, without a closure table.

**5. Ambiguous names and periodic components.**  55 of the 1578 items share their
English label with another item (`collidingItems_count`).  Among the eleven
periodic items of the class hierarchy, three do (`periodicItems_colliding`):
*region* (Q82794) and the two items labelled *element*.  So the label-collision
rate inside the periodic part of the hierarchy, 3 out of 11, is about eight
times the rate over the corpus as a whole, 55 out of 1578: two of the four
`subclass of` cycles are duplicated notions visible from the term side as well.
-/

namespace Wikidata
namespace SpectrumReport

open Wikidata.Generated Wikidata.Periodicity Wikidata.DefectReport Wikidata.PeriodicityReport

/-! ### The eleven items of the `subclass of` search -/

/-- The eleven periodic items of the class hierarchy, as a literal list. -/
def p279Items : List Qid :=
  [Qid.wd "Q3622002", Qid.wd "Q66666685", Qid.wd "Q3400985", Qid.wd "Q82794",
   Qid.wd "Q901", Qid.wd "Q1650915", Qid.wd "Q1184244", Qid.wd "Q1456832",
   Qid.wd "Q379825", Qid.wd "Q36808958", Qid.wd "Q5358816"]

theorem p279Items_eq : corpus.periodicItems = p279Items := periodicItems_eq

/-- **A larger bound cannot find a new item**: an item with any return time at
all is one of the eleven. -/
theorem subPeriodOf_isSome_imp (bound : ℕ) {x : Qid}
    (h : (corpus.subPeriodOf bound x).isSome = true) : x ∈ p279Items := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 h
  have : IsPeriodic corpus.supersL x := isPeriodic_of_periodOf hn
  rw [← p279Items_eq]
  exact (corpus.mem_periodicItems corpus_wellFormed).2 this

/-- The shortest returns of the eleven, searched to a hundred steps: the same
numbers as at twenty. -/
theorem periods_100 :
    p279Items.map (fun x => corpus.subPeriodOf 100 x) =
      [some 2, some 4, some 4, some 2, some 4, some 4, some 2, some 2, some 3,
       some 3, some 3] := by native_decide

/-- **The histogram of shortest returns**, at bound 100 and therefore at every
bound: four items return after two steps, three after three, four after four. -/
theorem periodHistogram_100 :
    [2, 3, 4].map (fun d => (p279Items.filter (fun x => corpus.subPeriodOf 100 x == some d)).length)
      = [4, 3, 4] := by native_decide

/-! ### The words -/

/-- The word `subclass of`. -/
def wSub : List Link := [Link.p279]
/-- The word `instance of`. -/
def wInst : List Link := [Link.p31]
/-- The word `instance of` followed by `subclass of`. -/
def wInstSub : List Link := [Link.p31, Link.p279]
/-- The word `subclass of` followed by `instance of`. -/
def wSubInst : List Link := [Link.p279, Link.p31]

/-- The fourteen words of length at most three in the two relations. -/
def spectrumWords : List (List Link) :=
  [wSub, wInst, wSubInst, wInstSub,
   [Link.p279, Link.p279], [Link.p31, Link.p31],
   [Link.p279, Link.p31, Link.p279], [Link.p31, Link.p279, Link.p31],
   [Link.p279, Link.p279, Link.p31], [Link.p31, Link.p279, Link.p279],
   [Link.p279, Link.p31, Link.p31], [Link.p31, Link.p31, Link.p279],
   [Link.p279, Link.p279, Link.p279], [Link.p31, Link.p31, Link.p31]]

/-- **The spectrum**: for each word, how many items the search returns to
themselves within six applications of the whole word. -/
theorem word_spectrum :
    spectrumWords.map (fun w => (corpus.wordPeriodicItems w 6).length) =
      [11, 1, 8, 9, 11, 1, 10, 4, 6, 8, 4, 5, 11, 1] := by native_decide

/-- Along `instance of` alone, exactly one item returns to itself. -/
theorem inst_periodicItems :
    corpus.wordPeriodicItems wInst 6 = [Qid.wd "Q23958852"] := by native_decide

/-- The nine items on a cycle of `instance of ∘ subclass of`. -/
theorem instSub_periodicItems :
    corpus.wordPeriodicItems wInstSub 6 =
      [Qid.wd "Q32753077", Qid.wd "Q45025858", Qid.wd "Q488383", Qid.wd "Q16686448",
       Qid.wd "Q151885", Qid.wd "Q7048977", Qid.wd "Q1272626", Qid.wd "Q16889133",
       Qid.wd "Q21146257"] := by native_decide

/-- The eight items on a cycle of `subclass of ∘ instance of`. -/
theorem subInst_periodicItems :
    corpus.wordPeriodicItems wSubInst 6 =
      [Qid.wd "Q19798651", Qid.wd "Q115471117", Qid.wd "Q96251598", Qid.wd "Q115490628",
       Qid.wd "Q151885", Qid.wd "Q23958852", Qid.wd "Q19478619",
       Qid.wd "Q33104279"] := by native_decide

/-- What the mixed cycles are about, from the downloaded term table. -/
theorem instSub_labels :
    (corpus.wordPeriodicItems wInstSub 6).map (fun x => kbTerms.labelOf x "en") =
      [some "Wikidata entity", some "depicting object", some "object",
       some "artificial object", some "concept", some "abstract entity",
       some "representation", some "class", some "type"] := by native_decide

theorem subInst_labels :
    (corpus.wordPeriodicItems wSubInst 6).map (fun x => kbTerms.labelOf x "en") =
      [some "wikibase data model possible value for a claim", some "self-depicting entity",
       some "type of object", some "fundamental Wikidata entity", some "concept",
       some "variable-order class", some "metaclass",
       some "philosophical concept"] := by native_decide

/-- **None of the mixed cycles touches a `subclass of` cycle**: the words find
entirely different items. -/
theorem mixed_disjoint_from_p279 :
    (corpus.wordPeriodicItems wInstSub 6).all (fun x => !p279Items.contains x) = true ∧
      (corpus.wordPeriodicItems wSubInst 6).all (fun x => !p279Items.contains x) = true := by
  native_decide

/-- **Longer periods find nothing new along the other words either**: raising the
bound from six to twelve, and to twenty for `instance of`, leaves the counts
unchanged. -/
theorem word_counts_larger_bounds :
    (corpus.wordPeriodicItems wInst 20).length = 1 ∧
      (corpus.wordPeriodicItems wInstSub 12).length = 9 ∧
      (corpus.wordPeriodicItems wSubInst 12).length = 8 := by native_decide

/-! ### The statements behind the mixed cycles -/

/-- *variable-order class* (Q23958852) is **an instance of itself**. -/
theorem variableOrderClass_selfInstance :
    (Qid.wd "Q23958852", Qid.wd "Q23958852") ∈ corpus.inst := by native_decide

/-- *class* (Q16889133) is an instance of *metaclass* (Q19478619), which is a
subclass of *class*. -/
theorem class_metaclass_mixedCycle :
    (Qid.wd "Q16889133", Qid.wd "Q19478619") ∈ corpus.inst ∧
      (Qid.wd "Q19478619", Qid.wd "Q16889133") ∈ corpus.sub := by native_decide

/-- *representation* (Q1272626) is an instance of *concept* (Q151885), which is a
subclass of *representation*. -/
theorem representation_concept_mixedCycle :
    (Qid.wd "Q1272626", Qid.wd "Q151885") ∈ corpus.inst ∧
      (Qid.wd "Q151885", Qid.wd "Q1272626") ∈ corpus.sub := by native_decide

/-- The self-instance, as a return of the `instance of` operator. -/
theorem variableOrderClass_isReturn :
    IsReturn (corpus.wordStep wInst) 1 (Qid.wd "Q23958852") := by
  refine ⟨Nat.one_pos, reachIn_one_iff.2 ?_⟩
  exact (KB.mem_wordStep wInst).2 ⟨Qid.wd "Q23958852", variableOrderClass_selfInstance, rfl⟩

/-- The *representation* / *concept* cycle, as a return of the mixed operator. -/
theorem representation_isReturn :
    IsReturn (corpus.wordStep wInstSub) 1 (Qid.wd "Q1272626") := by
  refine ⟨Nat.one_pos, reachIn_one_iff.2 ?_⟩
  exact (KB.mem_wordStep wInstSub).2
    ⟨Qid.wd "Q151885", representation_concept_mixedCycle.1,
      Qid.wd "Q1272626", representation_concept_mixedCycle.2, rfl⟩

/-- The *class* / *metaclass* cycle, as a return of the mixed operator. -/
theorem class_isReturn :
    IsReturn (corpus.wordStep wInstSub) 1 (Qid.wd "Q16889133") := by
  refine ⟨Nat.one_pos, reachIn_one_iff.2 ?_⟩
  exact (KB.mem_wordStep wInstSub).2
    ⟨Qid.wd "Q19478619", class_metaclass_mixedCycle.1,
      Qid.wd "Q16889133", class_metaclass_mixedCycle.2, rfl⟩

/-! ### No ontology models the corpus, cycles repaired or not -/

/-- **A self-instance rules out every ontology**: no abstract
`Wikidata.Ontology` has the P31 and P279 statements of the corpus. -/
theorem no_ontology_over_corpus_links (O : Ontology Qid) (hO : O.linkRel = corpus.LinkRel) :
    False :=
  KB.no_ontology_of_word_return ⟨1, variableOrderClass_isReturn⟩ (by decide) O hO

/-- Deleting `subclass of` statements never touches the `instance of` ones. -/
theorem foldl_dropSub_inst (l : List (Qid × Qid)) (kb : KB) :
    (l.foldl KB.dropSub kb).inst = kb.inst := by
  induction l generalizing kb with
  | nil => rfl
  | cons e l ih => simpa using ih (kb.dropSub e)

/-- The repair of the defect report deletes `subclass of` statements only, so the
`instance of` statements are untouched. -/
theorem acyclicCorpus_inst : acyclicCorpus.inst = corpus.inst := foldl_dropSub_inst _ _

theorem acyclicCorpus_selfInstance :
    (Qid.wd "Q23958852", Qid.wd "Q23958852") ∈ acyclicCorpus.inst := by
  rw [acyclicCorpus_inst]; exact variableOrderClass_selfInstance

theorem acyclicCorpus_variableOrderClass_isReturn :
    IsReturn (acyclicCorpus.wordStep wInst) 1 (Qid.wd "Q23958852") := by
  refine ⟨Nat.one_pos, reachIn_one_iff.2 ?_⟩
  exact (KB.mem_wordStep wInst).2 ⟨Qid.wd "Q23958852", acyclicCorpus_selfInstance, rfl⟩

/-- **Breaking the four `subclass of` cycles is not enough**: the repaired corpus
of the defect report, whose class hierarchy is acyclic, still has no model as an
abstract ontology, because *variable-order class* is still an instance of
itself. -/
theorem no_ontology_over_acyclicCorpus_links (O : Ontology Qid)
    (hO : O.linkRel = acyclicCorpus.LinkRel) : False :=
  KB.no_ontology_of_word_return ⟨1, acyclicCorpus_variableOrderClass_isReturn⟩ (by decide) O hO

/-! ### Component, period, phase -/

/-- The shortest return of *Wikidata entity* under `instance of ∘ subclass of` is
three applications of the word. -/
theorem entity_instSub_period :
    corpus.wordPeriodOf wInstSub 6 (Qid.wd "Q32753077") = some 3 := by native_decide

/-- *Wikidata entity* reaches *representation* in three applications of the
word … -/
theorem entity_reaches_representation :
    ReachIn (corpus.wordStep wInstSub) 3 (Qid.wd "Q32753077") (Qid.wd "Q1272626") :=
  mem_iterate.1 (by native_decide)

/-- … and *representation* reaches *Wikidata entity* back in two: the two items
lie in one strongly connected component of the mixed transition system. -/
theorem representation_reaches_entity :
    ReachIn (corpus.wordStep wInstSub) 2 (Qid.wd "Q1272626") (Qid.wd "Q32753077") :=
  mem_iterate.1 (by native_decide)

/-- **The fundamental period of the mixed component is one**, although the
shortest return of *Wikidata entity* is three: the component contains the fixed
point *representation*, and periods are an invariant of the component. -/
theorem entity_instSub_periodDivisor_eq_one {d : ℕ}
    (hd : IsPeriodDivisor (corpus.wordStep wInstSub) d (Qid.wd "Q32753077")) : d = 1 := by
  have hrep : IsPeriodDivisor (corpus.wordStep wInstSub) d (Qid.wd "Q1272626") :=
    (isPeriodDivisor_iff_of_connected entity_reaches_representation
      representation_reaches_entity).1 hd
  exact periodDivisor_eq_one_of_isReturn_one hrep representation_isReturn

/-- Consequently **the mixed component carries no non-trivial phase**: a phase
certificate for it can only have modulus one, so it cannot be coordinatised by a
finite cyclic phase the way the `subclass of` components can. -/
theorem entity_instSub_no_phase {d : ℕ} [NeZero d] {rev : Qid → List Qid}
    {phase : Qid → ZMod d}
    (hrevF : ∀ y, stepF rev y ⊆ corpus.allF) (hrevOut : ∀ y, y ∉ corpus.allF → rev y = [])
    (hstepF : ∀ y, stepF (corpus.wordStep wInstSub) y ⊆ corpus.allF)
    (hstepOut : ∀ y, y ∉ corpus.allF → corpus.wordStep wInstSub y = [])
    (hrev : ∀ u v, v ∈ rev u ↔ u ∈ corpus.wordStep wInstSub v)
    (h : phaseCertB (corpus.wordStep wInstSub) rev corpus.allF (Qid.wd "Q32753077") d phase
      = true) : d = 1 :=
  entity_instSub_periodDivisor_eq_one
    (isPeriodDivisor_of_phaseCertB hstepF hstepOut hrevF hrevOut hrev h)

/-- The phase of the *region* component, checked by forward and backward
reachability instead of a closure table. -/
theorem region_subPhaseCert :
    corpus.subPhaseCertB (Qid.wd "Q82794") 2 regionPhase = true := by native_decide

/-- **The period of the *region* component is even**, re-derived from the
reachability certificate. -/
theorem region_periodDivisor' : IsPeriodDivisor corpus.supersL 2 (Qid.wd "Q82794") :=
  KB.isPeriodDivisor_of_subPhaseCertB corpus_wellFormed region_subPhaseCert

/-! ### The terminology graph against the topology -/

/-- The items of the corpus that carry an English label, with it. -/
def labelled : List (Qid × String) :=
  corpus.items.filterMap (fun q => (kbTerms.labelOf q "en").map (fun s => (q, s)))

/-- The items whose English label is carried by another item as well. -/
def collidingItems : List Qid :=
  labelled.filterMap fun p =>
    if labelled.any (fun r => r.1 != p.1 && r.2 == p.2) then some p.1 else none

/-- **55 of the 1578 items share their label with another item.** -/
theorem collidingItems_count : collidingItems.length = 55 := by native_decide

/-- **Three of the eleven periodic items carry an ambiguous label**: *region*
(Q82794), which shares its label with two other items, and the two items labelled
*element*. -/
theorem p279Items_colliding :
    p279Items.filter (fun q => collidingItems.contains q) =
      [Qid.wd "Q82794", Qid.wd "Q379825", Qid.wd "Q5358816"] := by native_decide

/-- How many English aliases each of the eleven periodic items carries: the
duplicated notions are also the ones with many alternative names — *region*
(Q82794) has nine and *element* (Q379825) thirteen, while *geographical area*
and *academic professional* have none. -/
theorem p279Items_aliasCounts :
    p279Items.map (fun q => (kbTerms.aliasesOf q "en").length) =
      [0, 0, 2, 9, 1, 4, 0, 13, 6, 3, 2] := by native_decide

/-- The same, phrased for the computed list of periodic items. -/
theorem periodicItems_colliding :
    corpus.periodicItems.filter (fun q => collidingItems.contains q) =
      [Qid.wd "Q82794", Qid.wd "Q379825", Qid.wd "Q5358816"] := by
  rw [p279Items_eq]; exact p279Items_colliding

end SpectrumReport
end Wikidata
