import RequestProject.ItemMerge
import RequestProject.SelfDescription
import RequestProject.Reflection

/-!
# Renaming an ontology along an injection preserves and reflects everything

`KB.rename` (from `RequestProject.ItemMerge`) rewrites every statement of a
knowledge base along a map of identifiers. When that map merges two identifiers
the result can genuinely change — that is the point of item merges. This file
proves the complementary fact: when the map is **injective**, renaming is a pure
change of names.

For an injective `f` we show that membership, metaclass levels, the asserted
statements, their reflexive–transitive closures, the certified engine
(`isSubclassOf`, `isInstanceOf`) and every clause of the validator
(`wellFormed`, `levelsOk`, `acyclic`, `disjointOk`, hence `valid`) all transport
back and forth: `KB.valid_rename_iff`.

These are the technical lemmas behind `RequestProject.MetaFrobenius`, where the
injection is `Qid.about` and the renaming re-encodes an ontology inside its own
meta-vocabulary.
-/

namespace Wikidata
namespace KB

variable {kb : KB} {f : Qid → Qid}

/-! ### Functoriality of renaming -/

@[simp] theorem rename_name (kb : KB) (f : Qid → Qid) : (kb.rename f).name = kb.name := rfl
@[simp] theorem rename_items (kb : KB) (f : Qid → Qid) :
    (kb.rename f).items = kb.items.map f := rfl
@[simp] theorem rename_levels (kb : KB) (f : Qid → Qid) :
    (kb.rename f).levels = kb.levels.map (fun r => (f r.1, r.2)) := rfl
@[simp] theorem rename_sub (kb : KB) (f : Qid → Qid) :
    (kb.rename f).sub = kb.sub.map (fun r => (f r.1, f r.2)) := rfl
@[simp] theorem rename_inst (kb : KB) (f : Qid → Qid) :
    (kb.rename f).inst = kb.inst.map (fun r => (f r.1, f r.2)) := rfl
@[simp] theorem rename_disj (kb : KB) (f : Qid → Qid) :
    (kb.rename f).disj = kb.disj.map (fun r => (f r.1, f r.2)) := rfl

theorem rename_rename (kb : KB) (f g : Qid → Qid) :
    (kb.rename f).rename g = kb.rename (g ∘ f) := by
  simp [rename, List.map_map, Function.comp_def]

theorem rename_id (kb : KB) : kb.rename _root_.id = kb := by
  cases kb; simp [rename]

theorem rename_congr (kb : KB) {f g : Qid → Qid} (h : ∀ q, f q = g q) :
    kb.rename f = kb.rename g := by rw [funext h]

theorem rename_eq_self_of_forall {kb : KB} {f : Qid → Qid}
    (hi : ∀ q ∈ kb.items, f q = q) (hl : ∀ r ∈ kb.levels, f r.1 = r.1)
    (hs : ∀ r ∈ kb.sub, f r.1 = r.1 ∧ f r.2 = r.2)
    (hn : ∀ r ∈ kb.inst, f r.1 = r.1 ∧ f r.2 = r.2)
    (hd : ∀ r ∈ kb.disj, f r.1 = r.1 ∧ f r.2 = r.2) : kb.rename f = kb := by
  have map_id : ∀ (l : List Qid), (∀ q ∈ l, f q = q) → l.map f = l := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a t ih => simp [ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)), hl a (by simp)]
  have map_pair : ∀ (l : List (Qid × Qid)), (∀ r ∈ l, f r.1 = r.1 ∧ f r.2 = r.2) →
      l.map (fun r => (f r.1, f r.2)) = l := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a t ih =>
        obtain ⟨h1, h2⟩ := hl a (by simp)
        simp [ih (fun r hr => hl r (List.mem_cons_of_mem _ hr)), h1, h2]
  have map_lvl : ∀ (l : List (Qid × ℕ)), (∀ r ∈ l, f r.1 = r.1) →
      l.map (fun r => (f r.1, r.2)) = l := by
    intro l hl
    induction l with
    | nil => rfl
    | cons a t ih => simp [ih (fun r hr => hl r (List.mem_cons_of_mem _ hr)), hl a (by simp)]
  cases kb
  simp only [rename, KB.mk.injEq]
  exact ⟨trivial, map_id _ hi, map_lvl _ hl, map_pair _ hs, map_pair _ hn, map_pair _ hd⟩

/-! ### Membership and levels -/

theorem mem_items_rename_iff (hf : Function.Injective f) {a : Qid} :
    f a ∈ (kb.rename f).items ↔ a ∈ kb.items := by
  simp [List.mem_map_of_injective hf]

theorem exists_of_mem_items_rename {x : Qid} (h : x ∈ (kb.rename f).items) :
    ∃ a ∈ kb.items, x = f a := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (show x ∈ kb.items.map f from h)
  exact ⟨a, ha, rfl⟩

theorem lookup_map_inj {l : List (Qid × ℕ)} (hf : Function.Injective f) (q : Qid) :
    List.lookup (f q) (l.map (fun r => (f r.1, r.2))) = List.lookup q l := by
  induction l with
  | nil => rfl
  | cons r t ih =>
      by_cases h : q = r.1
      · subst h; rw [List.map_cons, lookup_cons_self, lookup_cons_self]
      · rw [List.map_cons, lookup_cons_ne (fun hh => h (hf hh)), lookup_cons_ne h, ih]

theorem levelOf_rename (hf : Function.Injective f) (q : Qid) :
    (kb.rename f).levelOf (f q) = kb.levelOf q := by
  show (List.lookup (f q) ((kb.rename f).levels)).getD 0 = (List.lookup q kb.levels).getD 0
  rw [rename_levels, lookup_map_inj hf]

/-! ### Statements -/

theorem sub_rename_exists {x z : Qid} (h : (kb.rename f).Sub x z) :
    ∃ u v, x = f u ∧ z = f v ∧ kb.Sub u v := by
  obtain ⟨r, hr, hre⟩ :=
    List.mem_map.1 (show (x, z) ∈ kb.sub.map (fun r => (f r.1, f r.2)) from h)
  exact ⟨r.1, r.2, (congrArg Prod.fst hre).symm, (congrArg Prod.snd hre).symm, hr⟩

theorem inst_rename_exists {x z : Qid} (h : (kb.rename f).Inst x z) :
    ∃ u v, x = f u ∧ z = f v ∧ kb.Inst u v := by
  obtain ⟨r, hr, hre⟩ :=
    List.mem_map.1 (show (x, z) ∈ kb.inst.map (fun r => (f r.1, f r.2)) from h)
  exact ⟨r.1, r.2, (congrArg Prod.fst hre).symm, (congrArg Prod.snd hre).symm, hr⟩

theorem sub_rename_iff (hf : Function.Injective f) {a b : Qid} :
    (kb.rename f).Sub (f a) (f b) ↔ kb.Sub a b := by
  refine ⟨fun h => ?_, sub_rename⟩
  obtain ⟨u, v, hu, hv, huv⟩ := sub_rename_exists h
  rwa [hf hu, hf hv]

theorem inst_rename_iff (hf : Function.Injective f) {a c : Qid} :
    (kb.rename f).Inst (f a) (f c) ↔ kb.Inst a c := by
  refine ⟨fun h => ?_, inst_rename⟩
  obtain ⟨u, v, hu, hv, huv⟩ := inst_rename_exists h
  rwa [hf hu, hf hv]

theorem exists_of_reflTransGen_sub_rename (hf : Function.Injective f) {a y : Qid}
    (h : Relation.ReflTransGen (kb.rename f).Sub (f a) y) :
    ∃ b, y = f b ∧ Relation.ReflTransGen kb.Sub a b := by
  induction h with
  | refl => exact ⟨a, rfl, Relation.ReflTransGen.refl⟩
  | tail _ hstep ih =>
      obtain ⟨b, rfl, hab⟩ := ih
      obtain ⟨u, v, hu, rfl, huv⟩ := sub_rename_exists hstep
      have hbu : b = u := hf hu
      subst hbu
      exact ⟨v, rfl, hab.tail huv⟩

theorem reflTransGen_sub_rename_iff (hf : Function.Injective f) {a b : Qid} :
    Relation.ReflTransGen (kb.rename f).Sub (f a) (f b) ↔ Relation.ReflTransGen kb.Sub a b := by
  constructor
  · intro h
    obtain ⟨c, hc, hac⟩ := exists_of_reflTransGen_sub_rename hf h
    rwa [hf hc.symm] at hac
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hstep ih => exact ih.tail (sub_rename hstep)

/-! ### The validator -/

theorem wellFormed_rename_iff (hf : Function.Injective f) :
    (kb.rename f).wellFormed = true ↔ kb.wellFormed = true := by
  simp [wellFormed, List.all_map, Function.comp_def, List.mem_map, hf.eq_iff]

theorem wellFormed_rename (hf : Function.Injective f) (hwf : kb.wellFormed = true) :
    (kb.rename f).wellFormed = true := (wellFormed_rename_iff hf).2 hwf

theorem isSubclassOf_rename_iff (hf : Function.Injective f) (hwf : kb.wellFormed = true)
    {a b : Qid} :
    (kb.rename f).isSubclassOf (f a) (f b) = true ↔ kb.isSubclassOf a b = true := by
  rw [isSubclassOf_iff (wellFormed_rename hf hwf), isSubclassOf_iff hwf,
    reflTransGen_sub_rename_iff hf]

theorem isInstanceOf_rename_iff (hf : Function.Injective f) (hwf : kb.wellFormed = true)
    {a c : Qid} :
    (kb.rename f).isInstanceOf (f a) (f c) = true ↔ kb.isInstanceOf a c = true := by
  rw [isInstanceOf_iff (wellFormed_rename hf hwf), isInstanceOf_iff hwf]
  constructor
  · rintro ⟨d, hd, hdc⟩
    obtain ⟨u, v, hu, rfl, huv⟩ := inst_rename_exists hd
    rw [← hf hu] at huv
    exact ⟨v, huv, (reflTransGen_sub_rename_iff hf).1 hdc⟩
  · rintro ⟨d, hd, hdc⟩
    exact ⟨f d, inst_rename hd, (reflTransGen_sub_rename_iff hf).2 hdc⟩

theorem levelsOk_rename_iff (hf : Function.Injective f) :
    (kb.rename f).levelsOk = true ↔ kb.levelsOk = true := by
  simp [levelsOk, List.all_map, Function.comp_def, levelOf_rename hf]

theorem acyclic_iff (kb : KB) : kb.acyclic = true ↔
    ∀ a ∈ kb.items, ∀ b ∈ kb.items,
      kb.isSubclassOf a b = true → kb.isSubclassOf b a = true → a = b := by
  simp only [acyclic, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    Bool.and_eq_false_imp, beq_iff_eq]
  constructor
  · intro h a ha b hb hab hba
    have := h a ha b hb
    simp [hab, hba] at this
    exact this
  · intro h a ha b hb
    by_cases hab : kb.isSubclassOf a b = true
    · by_cases hba : kb.isSubclassOf b a = true
      · simp [h a ha b hb hab hba]
      · simp [hab, Bool.eq_false_iff.2 hba]
    · simp [Bool.eq_false_iff.2 hab]

theorem acyclic_rename_iff (hf : Function.Injective f) (hwf : kb.wellFormed = true) :
    (kb.rename f).acyclic = true ↔ kb.acyclic = true := by
  rw [acyclic_iff, acyclic_iff]
  constructor
  · intro h a ha b hb hab hba
    have h' := h (f a) (mem_items_rename_iff hf |>.2 ha) (f b) (mem_items_rename_iff hf |>.2 hb)
      ((isSubclassOf_rename_iff hf hwf).2 hab) ((isSubclassOf_rename_iff hf hwf).2 hba)
    exact hf h'
  · intro h x hx y hy hxy hyx
    obtain ⟨a, ha, rfl⟩ := exists_of_mem_items_rename hx
    obtain ⟨b, hb, rfl⟩ := exists_of_mem_items_rename hy
    exact congrArg f (h a ha b hb ((isSubclassOf_rename_iff hf hwf).1 hxy)
      ((isSubclassOf_rename_iff hf hwf).1 hyx))

theorem disjointOk_iff (kb : KB) : kb.disjointOk = true ↔
    ∀ p ∈ kb.disj, ∀ a ∈ kb.items,
      ¬ (kb.isInstanceOf a p.1 = true ∧ kb.isInstanceOf a p.2 = true) := by
  constructor
  · intro h p hp a ha hcon
    have hb := List.all_eq_true.1 (List.all_eq_true.1 h p hp) a ha
    rw [hcon.1, hcon.2] at hb
    simp at hb
  · intro h
    refine List.all_eq_true.2 fun p hp => List.all_eq_true.2 fun a ha => ?_
    have hn := h p hp a ha
    by_cases h1 : kb.isInstanceOf a p.1 = true
    · by_cases h2 : kb.isInstanceOf a p.2 = true
      · exact absurd ⟨h1, h2⟩ hn
      · simp [Bool.eq_false_iff.2 h2]
    · simp [Bool.eq_false_iff.2 h1]

theorem disjointOk_rename_iff (hf : Function.Injective f) (hwf : kb.wellFormed = true) :
    (kb.rename f).disjointOk = true ↔ kb.disjointOk = true := by
  rw [disjointOk_iff, disjointOk_iff]
  constructor
  · rintro h p hp a ha ⟨h1, h2⟩
    refine h (f p.1, f p.2) (List.mem_map.2 ⟨p, hp, rfl⟩) (f a)
      ((mem_items_rename_iff hf).2 ha) ⟨?_, ?_⟩
    · exact (isInstanceOf_rename_iff hf hwf).2 h1
    · exact (isInstanceOf_rename_iff hf hwf).2 h2
  · rintro h q hq x hx ⟨h1, h2⟩
    obtain ⟨p, hp, hpe⟩ :=
      List.mem_map.1 (show q ∈ kb.disj.map (fun r => (f r.1, f r.2)) from hq)
    obtain ⟨a, ha, rfl⟩ := exists_of_mem_items_rename hx
    refine h p hp a ha ⟨?_, ?_⟩
    · refine (isInstanceOf_rename_iff hf hwf).1 ?_
      have : q.1 = f p.1 := by rw [← hpe]
      rwa [← this]
    · refine (isInstanceOf_rename_iff hf hwf).1 ?_
      have : q.2 = f p.2 := by rw [← hpe]
      rwa [← this]

/-- **Renaming along an injection preserves and reflects validity.** -/
theorem valid_rename_iff (hf : Function.Injective f) :
    (kb.rename f).valid = true ↔ kb.valid = true := by
  by_cases hwf : kb.wellFormed = true
  · simp only [valid, Bool.and_eq_true, wellFormed_rename_iff hf, levelsOk_rename_iff hf,
      acyclic_rename_iff hf hwf, disjointOk_rename_iff hf hwf]
  · have h1 : (kb.rename f).wellFormed = false := by
      rw [Bool.eq_false_iff]
      exact fun h => hwf ((wellFormed_rename_iff hf).1 h)
    simp [valid, h1, Bool.eq_false_iff.2 hwf]

end KB
end Wikidata
