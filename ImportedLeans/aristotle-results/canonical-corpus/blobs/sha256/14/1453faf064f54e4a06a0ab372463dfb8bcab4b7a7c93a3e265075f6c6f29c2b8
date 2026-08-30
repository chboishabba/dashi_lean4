import RequestProject.Defects
import RequestProject.Normalize
import RequestProject.Generated.Core
import RequestProject.Generated.Structures
import RequestProject.Generated.Frontier
import RequestProject.Generated.Frontier2
import RequestProject.Generated.Frontier3
import RequestProject.Generated.Frontier4
import RequestProject.Generated.VocabularyCorpus
import RequestProject.Generated.RelatedStructures
import RequestProject.Generated.RelatedStructures2
import RequestProject.Generated.KnowledgeRepresentation
import RequestProject.Generated.Theories
import RequestProject.Generated.Enriched

/-!
# The defect report: what the scan found in the downloaded Wikidata data

This module runs the checks of `RequestProject.Defects` over **all** the Wikidata
data this project has downloaded — the twelve compiled fragments merged and
deduplicated into `DefectReport.corpus` — and records the result.  Every number
below is decided by computation on the data, not asserted.

The findings, in the order they are proved:

* the corpus has 1578 items, 2257 `subclass of` and 1169 `instance of`
  statements (`corpus_size`), and is well formed (`corpus_wellFormed`);
* **11 items lie on a `subclass of` cycle** (`cyclicItems_count`), in four
  strongly connected groups whose statements are listed individually
  (`geographicalArea_cycle`, `scientist_cycle`, `element_cycle`, `delict_cycle`);
  consequently no abstract `Wikidata.Ontology` has exactly these `subclass of`
  statements (`no_ontology_over_corpus`);
* **234 `subclass of` statements are redundant** (`redundant_count`): the
  hierarchy already derives them from other statements;
* **deleting all 234 at once would lose knowledge** (`bulk_prune_not_lossless`)
  — the cycles are the reason: inside a cycle every statement looks redundant,
  and deleting them all disconnects it;
* **deleting four statements breaks all four cycles** (`cycleBreak_asserted`,
  `acyclicCorpus_acyclic`), and after that the bulk deletion *is* lossless: the
  226 statements that remain redundant (`acyclic_redundant_count`) can all be
  deleted together and every derived `subclass of` and `instance of` fact over
  the 1578 items is unchanged (`acyclic_prune_lossless`,
  `pruned_answers_subclass`, `pruned_answers_instance`), taking the hierarchy
  from 2253 to 2027 statements (`pruned_size`);
* **17 pairs are asserted both `instance of` and `subclass of`**
  (`instAndSub_count`), which cannot both be intended;
* and the same three counts, fragment by fragment, are in
  `fragment_defect_counts`.
-/

namespace Wikidata
namespace DefectReport

open Wikidata.Generated

/-! ### The corpus under scan -/

/-- Everything this project has downloaded from Wikidata: the twelve compiled
fragments, merged and deduplicated. -/
def corpus : KB :=
  (((((((((((Core.kb.merge Structures.kb).merge Frontier.kb).merge Frontier2.kb).merge
    Frontier3.kb).merge Frontier4.kb).merge VocabularyCorpus.kb).merge
    RelatedStructures.kb).merge RelatedStructures2.kb).merge
    KnowledgeRepresentation.kb).merge Theories.kb).merge Enriched.kb).normalize

theorem corpus_size :
    corpus.items.length = 1578 ∧ corpus.sub.length = 2257 ∧ corpus.inst.length = 1169 := by
  native_decide

/-- Every statement of the corpus is about a declared item, so the certified
queries apply to it. -/
theorem corpus_wellFormed : corpus.wellFormed = true := by native_decide

/-! ### Finding 1: cycles in the class hierarchy -/

/-- **Eleven items of the downloaded data lie on a `subclass of` cycle.** -/
theorem cyclicItems_count : corpus.cyclicItems.length = 11 := by native_decide

/-- The four cycles, as the statements Wikidata actually makes.  *region*
(Q82794) and *geographical area* (Q3622002) are subclasses of each other. -/
theorem geographicalArea_cycle :
    (Qid.wd "Q82794", Qid.wd "Q3622002") ∈ corpus.sub ∧
      (Qid.wd "Q3622002", Qid.wd "Q82794") ∈ corpus.sub := by native_decide

/-- *scientist* (Q901) ⊑ *researcher* (Q1650915) ⊑ *academic professional*
(Q66666685) ⊑ *academic* (Q3400985) ⊑ *scientist*: a cycle of length four. -/
theorem scientist_cycle :
    (Qid.wd "Q901", Qid.wd "Q1650915") ∈ corpus.sub ∧
      (Qid.wd "Q1650915", Qid.wd "Q66666685") ∈ corpus.sub ∧
      (Qid.wd "Q66666685", Qid.wd "Q3400985") ∈ corpus.sub ∧
      (Qid.wd "Q3400985", Qid.wd "Q901") ∈ corpus.sub := by native_decide

/-- *element* (Q379825) ⊑ *element* (Q5358816) ⊑ *element of set* (Q36808958) ⊑
*element* (Q379825): three items for one notion, in a cycle. -/
theorem element_cycle :
    (Qid.wd "Q379825", Qid.wd "Q5358816") ∈ corpus.sub ∧
      (Qid.wd "Q5358816", Qid.wd "Q36808958") ∈ corpus.sub ∧
      (Qid.wd "Q36808958", Qid.wd "Q379825") ∈ corpus.sub := by native_decide

/-- *delict* (Q1184244) and *violation of law* (Q1456832) are subclasses of each
other. -/
theorem delict_cycle :
    (Qid.wd "Q1184244", Qid.wd "Q1456832") ∈ corpus.sub ∧
      (Qid.wd "Q1456832", Qid.wd "Q1184244") ∈ corpus.sub := by native_decide

theorem cyclicItems_ne_nil : corpus.cyclicItems ≠ [] := by
  intro h
  have := cyclicItems_count
  rw [h] at this
  exact absurd this (by decide)

/-- **The cycles are errors, not matters of taste**: no abstract Wikidata
ontology has exactly these `subclass of` statements, because the class hierarchy
of an `Ontology` is antisymmetric. -/
theorem no_ontology_over_corpus (O : Ontology Qid) (h : O.P279 = corpus.Sub) : False := by
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ cyclicItems_ne_nil
  exact KB.no_ontology_of_cyclicItems corpus_wellFormed ha O h

/-! ### Finding 2: redundant `subclass of` statements -/

/-- **234 of the 2257 `subclass of` statements are redundant**: the value is
already reachable from the subject through another direct superclass. -/
theorem redundant_count : corpus.redundantSubLFast.length = 234 := by native_decide

/-- **They cannot all be deleted at once**, and the tool says so rather than
guessing: the bulk deletion changes what the corpus derives. -/
theorem bulk_prune_not_lossless : corpus.prunePreservesB = false := by native_decide

/-! ### The fix: break the cycles first, then prune -/

/-- One statement from each of the four cycles.  In each case it is the
statement that reverses the intended direction, or that links two items which
duplicate one notion. -/
def cycleBreak : List (Qid × Qid) :=
  [(Qid.wd "Q3622002", Qid.wd "Q82794"), (Qid.wd "Q3400985", Qid.wd "Q901"),
   (Qid.wd "Q36808958", Qid.wd "Q379825"), (Qid.wd "Q1184244", Qid.wd "Q1456832")]

theorem cycleBreak_asserted : ∀ e ∈ cycleBreak, e ∈ corpus.sub := by native_decide

/-- The corpus with those four statements removed. -/
def acyclicCorpus : KB := cycleBreak.foldl KB.dropSub corpus

/-- **Four deletions remove every cycle.** -/
theorem acyclicCorpus_acyclic : acyclicCorpus.cyclicItems = [] := by native_decide

theorem acyclicCorpus_wellFormed : acyclicCorpus.wellFormed = true := by native_decide

/-- With the cycles gone, 226 statements are still redundant. -/
theorem acyclic_redundant_count : acyclicCorpus.redundantSubLFast.length = 226 := by
  native_decide

/-- **And now they can all be deleted at once**: the check passes. -/
theorem acyclic_prune_lossless : acyclicCorpus.prunePreservesB = true := by native_decide

/-- The hierarchy shrinks from 2253 to 2027 `subclass of` statements. -/
theorem pruned_size :
    acyclicCorpus.sub.length = 2253 ∧ acyclicCorpus.pruneRedundant.sub.length = 2027 := by
  native_decide

/-- **Nothing is lost**: after the 226 deletions every `subclass of` question
about declared items is answered exactly as before. -/
theorem pruned_answers_subclass (a b : Qid) :
    acyclicCorpus.pruneRedundant.isSubclassOf a b = acyclicCorpus.isSubclassOf a b :=
  KB.pruneRedundant_lossless acyclicCorpus_wellFormed acyclic_prune_lossless a b

/-- … and so is every `instance of` question. -/
theorem pruned_answers_instance (a c : Qid) :
    acyclicCorpus.pruneRedundant.isInstanceOf a c = acyclicCorpus.isInstanceOf a c :=
  KB.pruneRedundant_lossless_inst acyclicCorpus_wellFormed acyclic_prune_lossless a c

/-! ### Finding 3: `instance of` and `subclass of` between the same two items -/

/-- **17 pairs carry both a P31 and a P279 statement.**  An item is either a
member of a class or a kind of it; at most one of the two can be intended. -/
theorem instAndSub_count : corpus.instAndSubL.length = 17 := by native_decide

/-- A witness: *computer* (Q68) is stated to be both an instance and a subclass
of *machine* (Q11019). -/
theorem computer_instAndSub : (Qid.wd "Q68", Qid.wd "Q11019") ∈ corpus.instAndSubL := by
  native_decide

/-- A confused pair really is derived twice over. -/
theorem computer_derived_twice :
    corpus.isInstanceOf (Qid.wd "Q68") (Qid.wd "Q11019") = true ∧
      corpus.isSubclassOf (Qid.wd "Q68") (Qid.wd "Q11019") = true := by
  simpa using KB.instAndSubL_derives corpus_wellFormed computer_instAndSub

/-! ### The same counts, fragment by fragment -/

/-- For each downloaded fragment: the number of redundant `subclass of`
statements, of items on a cycle, and of pairs asserted both ways. -/
theorem fragment_defect_counts :
    [Core.kb, Structures.kb, Frontier.kb, Frontier2.kb, Frontier3.kb, Frontier4.kb,
      VocabularyCorpus.kb, RelatedStructures.kb, RelatedStructures2.kb,
      KnowledgeRepresentation.kb, Theories.kb, Enriched.kb].map
        (fun kb => (kb.redundantSubLFast.length, kb.cyclicItems.length, kb.instAndSubL.length)) =
      [(65, 2, 6), (11, 0, 0), (41, 0, 3), (22, 0, 4), (6, 2, 2), (0, 0, 0),
       (32, 0, 3), (3, 0, 1), (2, 0, 1), (7, 0, 1), (13, 0, 1), (13, 0, 3)] := by
  native_decide

end DefectReport
end Wikidata
