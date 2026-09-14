import RequestProject.Modules
import RequestProject.DefTest

/-!
# Module extraction on the downloaded corpus

`RequestProject.Modules` proves that extracting the module about a set of items keeps
every `subclass of` and `instance of` consequence about them. This file runs that
extraction on the merged corpus of `RequestProject.DefTest` — 1578 items, 2257 `subclass
of` and 1169 `instance of` statements downloaded from Wikidata — and measures what it
saves.

The module about *mathematics* (`Q395`) has 279 items and 671 statements: a fifth of the
corpus, and by `Wikidata.KB.moduleOf_isSubclassOf` and
`Wikidata.KB.moduleOf_isInstanceOf` it answers every question about `Q395` exactly as the
whole corpus does (`mathModule_subclass_conservative`,
`mathModule_instance_conservative`). The corpus is only well formed, not valid — its
metaclass levels do not check out — and that is all conservativity needs.

The sizes are computed by `native_decide`, so they are facts about the downloaded data.
-/

namespace Wikidata
namespace ModulesCorpus

open KB DefTest

/-- The merged corpus is well formed: every statement mentions declared items. -/
theorem corpus_wellFormed : corpus.wellFormed = true := by native_decide

/-! ### The module about mathematics -/

/-- `mathematics` (`Q395`). -/
def mathematics : Qid := .wd "Q395"

/-- The module of the corpus about `mathematics`. -/
def mathModule : KB := corpus.moduleOf [mathematics]

/-- The module about mathematics is a fifth of the corpus: 279 of the 1578 items, 405 of
the 2257 `subclass of` and 266 of the 1169 `instance of` statements. -/
theorem mathModule_size :
    mathModule.items.length = 279 ∧ mathModule.sub.length = 405 ∧
      mathModule.inst.length = 266 := by native_decide

/-- Nothing is lost: about `mathematics`, the module derives exactly the `subclass of`
facts the whole corpus derives. -/
theorem mathModule_subclass_conservative (b : Qid) :
    mathModule.isSubclassOf mathematics b = corpus.isSubclassOf mathematics b :=
  moduleOf_isSubclassOf corpus_wellFormed (seed_mem_moduleItemsF (by simp)) b

/-- The same for the instance relation. -/
theorem mathModule_instance_conservative (c : Qid) :
    mathModule.isInstanceOf mathematics c = corpus.isInstanceOf mathematics c :=
  moduleOf_isInstanceOf corpus_wellFormed (seed_mem_moduleItemsF (by simp)) c

/-- The extracted module is itself a well-formed knowledge base. -/
theorem mathModule_wellFormed : mathModule.wellFormed = true :=
  moduleOf_wellFormed corpus_wellFormed _

/-! ### Other modules, and how they combine -/

/-- `human` (`Q5`). -/
def human : Qid := .wd "Q5"

/-- The module about `human` has 267 items, and the module about `academic discipline`
(`Q11862829`) has 197. -/
theorem other_module_sizes :
    (corpus.moduleOf [human]).items.length = 267 ∧
      (corpus.moduleOf [.wd "Q11862829"]).items.length = 197 := by native_decide

/-- Extracting for two seeds at once is not the sum of the two extractions: the modules
about `mathematics` and `human` overlap, so together they have 345 items, not 546. -/
theorem joint_module_size :
    (corpus.moduleOf [mathematics, human]).items.length = 345 := by native_decide

/-- Extraction is monotone in the seeds: the module about mathematics sits inside the
module about mathematics and human. -/
theorem mathModule_subset_joint :
    corpus.moduleItemsF [mathematics] ⊆ corpus.moduleItemsF [mathematics, human] :=
  moduleItemsF_mono (by simp)

end ModulesCorpus
end Wikidata
