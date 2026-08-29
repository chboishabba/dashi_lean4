import RequestProject.Engine
import RequestProject.Merge

/-!
# Normalising a knowledge base

Importing several fragments of Wikidata and merging them produces a knowledge
base with repetitions: the same item, or the very same `subclass of` statement,
downloaded once per fragment.  `KB.normalize` removes those repetitions.

The point of the file is that normalisation is **invisible**: the normalised base
declares the same items (`KB.normalize_mem_items`), asserts the same statements
(`KB.normalize_Sub_eq`, `KB.normalize_Inst_eq`), answers every query the same way
(`KB.normalize_isSubclassOf`, `KB.normalize_isInstanceOf`) and gets the same
verdict from the validator (`KB.normalize_valid`).  Nothing is lost and nothing is
invented; only the duplicates go.
-/

namespace Wikidata
namespace KB

variable {kb : KB}

/-- A knowledge base with its repeated items and repeated statements removed.
The level table is left alone: `KB.levelOf` reads its first entry for an item, so
duplicates there are already invisible. -/
def normalize (kb : KB) : KB where
  name := kb.name
  items := kb.items.dedup
  levels := kb.levels
  sub := kb.sub.dedup
  inst := kb.inst.dedup
  disj := kb.disj.dedup

@[simp] theorem normalize_levels (kb : KB) : kb.normalize.levels = kb.levels := rfl

@[simp] theorem normalize_items (kb : KB) : kb.normalize.items = kb.items.dedup := rfl

@[simp] theorem normalize_sub (kb : KB) : kb.normalize.sub = kb.sub.dedup := rfl

@[simp] theorem normalize_inst (kb : KB) : kb.normalize.inst = kb.inst.dedup := rfl

@[simp] theorem normalize_disj (kb : KB) : kb.normalize.disj = kb.disj.dedup := rfl

@[simp] theorem normalize_levelOf (kb : KB) (q : Qid) : kb.normalize.levelOf q = kb.levelOf q :=
  rfl

@[simp] theorem normalize_mem_items {q : Qid} : q ∈ kb.normalize.items ↔ q ∈ kb.items :=
  List.mem_dedup

/-- Normalisation keeps exactly the `subclass of` statements. -/
theorem normalize_Sub_eq (kb : KB) : kb.normalize.Sub = kb.Sub := by
  funext a b
  exact propext (by simp [Sub, List.mem_dedup])

/-- Normalisation keeps exactly the `instance of` statements. -/
theorem normalize_Inst_eq (kb : KB) : kb.normalize.Inst = kb.Inst := by
  funext a c
  exact propext (by simp [Inst, List.mem_dedup])

/-- Normalisation keeps exactly the disjointness declarations. -/
theorem normalize_Disj_eq (kb : KB) : kb.normalize.Disj = kb.Disj := by
  funext c d
  exact propext (by simp [Disj, List.mem_dedup])

theorem normalize_wellFormed (hwf : kb.wellFormed = true) : kb.normalize.wellFormed = true := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    normalize_items, normalize_sub, normalize_inst, normalize_disj, List.mem_dedup] at hwf ⊢
  exact hwf

/-- **Queries are unaffected**: the normalised base decides `subclass of` exactly
as the original does. -/
theorem normalize_isSubclassOf (hwf : kb.wellFormed = true) (a b : Qid) :
    kb.normalize.isSubclassOf a b = kb.isSubclassOf a b := by
  rw [Bool.eq_iff_iff, isSubclassOf_iff (normalize_wellFormed hwf), isSubclassOf_iff hwf,
    normalize_Sub_eq]

/-- **Queries are unaffected**: the normalised base decides `instance of` exactly
as the original does. -/
theorem normalize_isInstanceOf (hwf : kb.wellFormed = true) (a c : Qid) :
    kb.normalize.isInstanceOf a c = kb.isInstanceOf a c := by
  rw [Bool.eq_iff_iff, isInstanceOf_iff (normalize_wellFormed hwf), isInstanceOf_iff hwf,
    normalize_Sub_eq, normalize_Inst_eq]

theorem normalize_levelsOk (kb : KB) : kb.normalize.levelsOk = kb.levelsOk := by
  rw [Bool.eq_iff_iff]
  simp only [levelsOk, Bool.and_eq_true, List.all_eq_true, normalize_sub, normalize_inst,
    List.mem_dedup, normalize_levelOf]

theorem normalize_acyclic (hwf : kb.wellFormed = true) : kb.normalize.acyclic = kb.acyclic := by
  rw [Bool.eq_iff_iff]
  simp only [acyclic, List.all_eq_true, normalize_items, List.mem_dedup,
    normalize_isSubclassOf hwf]

theorem normalize_disjointOk (hwf : kb.wellFormed = true) :
    kb.normalize.disjointOk = kb.disjointOk := by
  rw [Bool.eq_iff_iff]
  simp only [disjointOk, List.all_eq_true, normalize_items, normalize_disj, List.mem_dedup,
    normalize_isInstanceOf hwf]

/-- **The validator gives the same verdict** on a base and on its normalisation. -/
theorem normalize_valid (hwf : kb.wellFormed = true) : kb.normalize.valid = kb.valid := by
  simp only [valid, normalize_wellFormed hwf, hwf, normalize_levelsOk, normalize_acyclic hwf,
    normalize_disjointOk hwf]

/-- Normalisation loses no knowledge. -/
theorem normalize_entails (hwf : kb.wellFormed = true) : kb.normalize.Entails kb = true := by
  simp only [Entails, Bool.and_eq_true, List.all_eq_true, normalize_isSubclassOf hwf,
    normalize_isInstanceOf hwf]
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · exact (isSubclassOf_iff hwf p.1 p.2).2 (Relation.ReflTransGen.single hp)
  · exact (isInstanceOf_iff hwf p.1 p.2).2 ⟨p.2, hp, Relation.ReflTransGen.refl⟩

/-- And it adds none: the original entails the normalisation. -/
theorem entails_normalize (hwf : kb.wellFormed = true) : kb.Entails kb.normalize = true := by
  simp only [Entails, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · exact (isSubclassOf_iff hwf p.1 p.2).2
      (Relation.ReflTransGen.single (by simpa [normalize_Sub_eq] using (show kb.normalize.Sub p.1 p.2 from hp)))
  · refine (isInstanceOf_iff hwf p.1 p.2).2 ⟨p.2, ?_, Relation.ReflTransGen.refl⟩
    simpa [normalize_Inst_eq] using (show kb.normalize.Inst p.1 p.2 from hp)

end KB
end Wikidata
