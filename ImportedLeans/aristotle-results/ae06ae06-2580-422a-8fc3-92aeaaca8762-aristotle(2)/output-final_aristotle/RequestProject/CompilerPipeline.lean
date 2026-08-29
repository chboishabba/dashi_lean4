import RequestProject.ProgramAlgebra
import RequestProject.SpectrumReport

/-!
# Compilation as a chain of representations

The repair of the defect report is a two-stage pipeline on knowledge bases:

```
corpus  --(delete four cyclic statements)-->  repaired  --(delete the redundant ones)-->  compiled
```

This module reads it as a *compiler* — a chain of representations of the same
program — and records what each stage preserves.  Nothing here needs a new
computation over the data: the stages are filters of the statement lists, so the
morphism properties are structural, and the semantic invariants are the
losslessness theorems already proved in `RequestProject.DefectReport`.

* `compiled_sub_subset`, `compiled_inst` — each stage only deletes `subclass of`
  statements and never touches `instance of`;
* `wordStep_compiled_mono` — **every stage is a morphism of transformation
  algebras**: a run of any word of `RequestProject.RelationWords` in the compiled
  base is a run of the same word in the source;
* `compiled_answers_subclass`, `compiled_answers_instance` — the compiled base
  answers **every** derived `subclass of` and `instance of` question exactly as
  the repaired one does: the optimisation is semantics-preserving;
* `compiled_size` — and it is a real optimisation: 2257 `subclass of` statements
  in the source, 2253 after the repair, 2027 after the pruning.
-/

namespace Wikidata
namespace CompilerPipeline

open Wikidata.DefectReport

/-- The first stage: delete the four statements that close the cycles. -/
def repaired (kb : KB) : KB := cycleBreak.foldl KB.dropSub kb

/-- The second stage: delete every redundant `subclass of` statement. -/
def compiled (kb : KB) : KB := (repaired kb).pruneRedundant

theorem repaired_corpus : repaired corpus = acyclicCorpus := rfl

theorem compiled_corpus : compiled corpus = acyclicCorpus.pruneRedundant := rfl

/-! ### Each stage is a morphism -/

theorem foldl_dropSub_sub_subset (l : List (Qid × Qid)) (kb : KB) {e : Qid × Qid}
    (he : e ∈ (l.foldl KB.dropSub kb).sub) : e ∈ kb.sub := by
  induction l generalizing kb with
  | nil => exact he
  | cons f l ih => exact KB.dropSub_sub_subset (ih (kb.dropSub f) he)

theorem pruneRedundant_sub_subset {kb : KB} {e : Qid × Qid} (he : e ∈ kb.pruneRedundant.sub) :
    e ∈ kb.sub :=
  (List.mem_filter.1 he).1

@[simp] theorem pruneRedundant_inst (kb : KB) : kb.pruneRedundant.inst = kb.inst := rfl

/-- The compiled base makes no `subclass of` statement the source does not
make. -/
theorem compiled_sub_subset {kb : KB} {e : Qid × Qid} (he : e ∈ (compiled kb).sub) :
    e ∈ kb.sub :=
  foldl_dropSub_sub_subset _ _ (pruneRedundant_sub_subset he)

/-- The `instance of` statements pass through the pipeline untouched. -/
theorem compiled_inst (kb : KB) : (compiled kb).inst = kb.inst := by
  rw [compiled, pruneRedundant_inst, repaired, SpectrumReport.foldl_dropSub_inst]

/-- **Compilation is a morphism of transformation algebras**: every run of a
relation word in the compiled base is a run of the same word in the source. -/
theorem wordStep_compiled_mono (kb : KB) (w : List Link) (x y : Qid)
    (h : y ∈ (compiled kb).wordStep w x) : y ∈ kb.wordStep w x := by
  refine KB.wordStep_mono (fun e he => compiled_sub_subset he) (fun e he => ?_) w x y h
  rwa [compiled_inst] at he

/-! ### What the pipeline preserves, and what it removes -/

/-- The compiled corpus answers every derived `subclass of` question exactly as
the repaired one does. -/
theorem compiled_answers_subclass (a b : Qid) :
    (compiled corpus).isSubclassOf a b = (repaired corpus).isSubclassOf a b :=
  pruned_answers_subclass a b

/-- … and every derived `instance of` question. -/
theorem compiled_answers_instance (a c : Qid) :
    (compiled corpus).isInstanceOf a c = (repaired corpus).isInstanceOf a c :=
  pruned_answers_instance a c

/-- The three representations of the same hierarchy: 2257 statements in the
source, 2253 after the repair, 2027 after the pruning. -/
theorem compiled_size :
    corpus.sub.length = 2257 ∧ (repaired corpus).sub.length = 2253 ∧
      (compiled corpus).sub.length = 2027 :=
  ⟨corpus_size.2.1, pruned_size.1, pruned_size.2⟩

end CompilerPipeline
end Wikidata
