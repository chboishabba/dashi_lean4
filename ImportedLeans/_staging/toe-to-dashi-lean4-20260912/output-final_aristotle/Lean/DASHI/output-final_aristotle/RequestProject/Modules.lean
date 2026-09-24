import RequestProject.Merge

/-!
# Module extraction: a self-contained sub-ontology about a chosen set of items

Wikidata is far too large to reason about as a whole, and the practical answer — the
same one taken in ontology engineering generally — is *module extraction*: given a
signature (a handful of items one cares about), carve out the part of the ontology that
carries all the ontological consequences about them, and forget the rest.

This file adds such an extraction to the executable engine of `RequestProject.Engine`,
and proves that it does what it is supposed to do.

* `Wikidata.KB.Dep` is the dependency step: a direct `subclass of` (P279) or
  `instance of` (P31) statement out of an item. `Wikidata.KB.moduleItemsF` is the set of
  items reachable from the seeds along it, computed by the certified saturation of
  `RequestProject.Reachability` and characterised abstractly by
  `Wikidata.KB.mem_moduleItemsF_iff`.
* `Wikidata.KB.moduleOf kb S` is the extracted module: those items, with every statement
  of `kb` issuing from them.
* **Soundness** (`Wikidata.KB.moduleOf_isSubclassOf_le`,
  `Wikidata.KB.moduleOf_isInstanceOf_le`): the module never invents a fact — everything
  it derives, the full base derives.
* **Completeness / conservativity** (`Wikidata.KB.moduleOf_isSubclassOf`,
  `Wikidata.KB.moduleOf_isInstanceOf`): about an item of the module, the module derives
  *exactly* the same `subclass of` and `instance of` facts as the whole base. Extraction
  therefore loses nothing one wanted to know.
* The lists the engine prints agree as well (`Wikidata.KB.moduleOf_superclassesOfL`,
  `Wikidata.KB.moduleOf_classesOf`).
* **Validity is preserved** (`Wikidata.KB.moduleOf_valid`): a module of a validated
  knowledge base passes the validator, so it is again an abstract
  `Wikidata.Ontology` and every theorem of `RequestProject.Core` applies to it.
* The base entails every module of it (`Wikidata.KB.entails_moduleOf`): extraction never
  adds knowledge.
* Structural laws: the extraction is monotone in the seeds
  (`Wikidata.KB.moduleItemsF_mono`), idempotent
  (`Wikidata.KB.moduleOf_moduleItemsF`), and extracting over all items returns the base
  itself (`Wikidata.KB.moduleOf_items_self`).

`RequestProject.ModulesExamples` runs the extraction on the worked Wikidata fragment.
-/

namespace Wikidata
namespace KB

/-! ### The dependency relation -/

variable (kb : KB)

/-- The dependency step: a direct `subclass of` or `instance of` statement. -/
def Dep (a b : Qid) : Prop := kb.Sub a b ∨ kb.Inst a b

instance (a b : Qid) : Decidable (kb.Dep a b) := by
  unfold Dep Sub Inst; infer_instance

/-- The successors of an item along the dependency relation, computably. -/
def depSucc (q : Qid) : Finset Qid := kb.supers q ∪ (kb.directClassesL q).toFinset

variable {kb}

theorem mem_depSucc {a b : Qid} : b ∈ kb.depSucc a ↔ kb.Dep a b := by
  simp [depSucc, Dep, mem_supers, mem_directClassesL]

theorem depSucc_eq_dep (kb : KB) : (fun u v => v ∈ kb.depSucc u) = kb.Dep := by
  funext u v; exact propext mem_depSucc

theorem dep_mem_items (hwf : kb.wellFormed = true) {a b : Qid} (h : kb.Dep a b) :
    a ∈ kb.items ∧ b ∈ kb.items := by
  rcases h with h | h
  · exact wf_sub hwf h
  · exact wf_inst hwf h

theorem depSucc_subset_all (hwf : kb.wellFormed = true) (y : Qid) : kb.depSucc y ⊆ kb.allF := by
  intro b hb
  exact mem_allF.2 (dep_mem_items hwf (mem_depSucc.1 hb)).2

theorem depSucc_eq_empty_of_not_mem (hwf : kb.wellFormed = true) {y : Qid} (hy : y ∉ kb.allF) :
    kb.depSucc y = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 fun b hb => ?_
  exact hy (mem_allF.2 (dep_mem_items hwf (mem_depSucc.1 hb)).1)

/-! ### The items of a module -/

variable (kb)

/-- The items of the module extracted for the seeds `S`: everything reachable from a
seed along `subclass of` and `instance of` statements. -/
def moduleItemsF (S : List Qid) : Finset Qid :=
  S.toFinset.biUnion (fun s => Reach.reach kb.depSucc kb.allF s)

variable {kb}

/-- **What the module contains**: exactly the items reachable from a seed along the
`subclass of` / `instance of` statements. -/
theorem mem_moduleItemsF_iff (hwf : kb.wellFormed = true) {S : List Qid} {q : Qid} :
    q ∈ kb.moduleItemsF S ↔ ∃ s ∈ S, Relation.ReflTransGen kb.Dep s q := by
  have h : ∀ s, q ∈ Reach.reach kb.depSucc kb.allF s ↔ Relation.ReflTransGen kb.Dep s q := by
    intro s
    have := Reach.mem_reach_iff_of_closed kb.depSucc (depSucc_subset_all hwf)
      (fun y hy => depSucc_eq_empty_of_not_mem hwf hy) s q
    rwa [depSucc_eq_dep] at this
  simp [moduleItemsF, Finset.mem_biUnion, h]

theorem seed_mem_moduleItemsF {S : List Qid} {s : Qid} (hs : s ∈ S) :
    s ∈ kb.moduleItemsF S :=
  Finset.mem_biUnion.2 ⟨s, List.mem_toFinset.2 hs, Reach.mem_reach_self _ _ _⟩

/-- The items of a module are closed under the dependency relation. -/
theorem moduleItemsF_closed (hwf : kb.wellFormed = true) {S : List Qid} {a b : Qid}
    (ha : a ∈ kb.moduleItemsF S) (h : kb.Dep a b) : b ∈ kb.moduleItemsF S := by
  obtain ⟨s, hs, hpath⟩ := (mem_moduleItemsF_iff hwf).1 ha
  exact (mem_moduleItemsF_iff hwf).2 ⟨s, hs, hpath.tail h⟩

/-- The items of a module are closed under derived `subclass of`. -/
theorem moduleItemsF_closed_sub (hwf : kb.wellFormed = true) {S : List Qid} {a b : Qid}
    (ha : a ∈ kb.moduleItemsF S) (h : Relation.ReflTransGen kb.Sub a b) :
    b ∈ kb.moduleItemsF S := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact moduleItemsF_closed hwf ih (Or.inl hbc)

/-- The items of a module are closed under chains of dependency steps. -/
theorem moduleItemsF_closed_path (hwf : kb.wellFormed = true) {S : List Qid} {a b : Qid}
    (ha : a ∈ kb.moduleItemsF S) (h : Relation.ReflTransGen kb.Dep a b) :
    b ∈ kb.moduleItemsF S := by
  induction h with
  | refl => exact ha
  | tail _ hbc ih => exact moduleItemsF_closed hwf ih hbc

theorem moduleItemsF_mono {S T : List Qid} (h : ∀ s ∈ S, s ∈ T) :
    kb.moduleItemsF S ⊆ kb.moduleItemsF T := by
  intro q hq
  obtain ⟨s, hs, hq'⟩ := Finset.mem_biUnion.1 hq
  exact Finset.mem_biUnion.2 ⟨s, List.mem_toFinset.2 (h s (List.mem_toFinset.1 hs)), hq'⟩

theorem moduleItemsF_subset_items (hwf : kb.wellFormed = true) {S : List Qid}
    (hS : ∀ s ∈ S, s ∈ kb.items) {q : Qid} (hq : q ∈ kb.moduleItemsF S) : q ∈ kb.items := by
  obtain ⟨s, hs, hpath⟩ := (mem_moduleItemsF_iff hwf).1 hq
  induction hpath with
  | refl => exact hS s hs
  | tail _ hbc _ => exact (dep_mem_items hwf hbc).2

/-! ### The extracted module -/

/-- The module of `kb` extracted for the seeds `S`: the items reachable from the seeds,
together with every statement of `kb` issuing from such an item. The level table is kept
as it is, so that levels are unchanged. -/
def moduleOf (kb : KB) (S : List Qid) : KB :=
  let M := kb.moduleItemsF S
  { name := kb.name ++ " (module)"
    items := kb.items.filter (fun q => decide (q ∈ M))
    levels := kb.levels
    sub := kb.sub.filter (fun p => decide (p.1 ∈ M))
    inst := kb.inst.filter (fun p => decide (p.1 ∈ M))
    disj := kb.disj.filter (fun p => decide (p.1 ∈ M) && decide (p.2 ∈ M)) }

@[simp] theorem moduleOf_levelOf (kb : KB) (S : List Qid) (q : Qid) :
    (kb.moduleOf S).levelOf q = kb.levelOf q := rfl

theorem mem_moduleOf_items {S : List Qid} {q : Qid} :
    q ∈ (kb.moduleOf S).items ↔ q ∈ kb.items ∧ q ∈ kb.moduleItemsF S := by
  simp [moduleOf, List.mem_filter]

theorem moduleOf_Sub_iff {S : List Qid} {a b : Qid} :
    (kb.moduleOf S).Sub a b ↔ kb.Sub a b ∧ a ∈ kb.moduleItemsF S := by
  simp [Sub, moduleOf, List.mem_filter]

theorem moduleOf_Inst_iff {S : List Qid} {a c : Qid} :
    (kb.moduleOf S).Inst a c ↔ kb.Inst a c ∧ a ∈ kb.moduleItemsF S := by
  simp [Inst, moduleOf, List.mem_filter]

theorem moduleOf_Sub_le {S : List Qid} {a b : Qid} (h : (kb.moduleOf S).Sub a b) : kb.Sub a b :=
  (moduleOf_Sub_iff.1 h).1

theorem moduleOf_Inst_le {S : List Qid} {a c : Qid} (h : (kb.moduleOf S).Inst a c) : kb.Inst a c :=
  (moduleOf_Inst_iff.1 h).1

theorem moduleOf_disj_le {S : List Qid} {c d : Qid} (h : (c, d) ∈ (kb.moduleOf S).disj) :
    (c, d) ∈ kb.disj := List.mem_of_mem_filter h

/-- A module of a well-formed knowledge base is well-formed. -/
theorem moduleOf_wellFormed (hwf : kb.wellFormed = true) (S : List Qid) :
    (kb.moduleOf S).wellFormed = true := by
  have hitem : ∀ {q : Qid}, q ∈ kb.items → q ∈ kb.moduleItemsF S → q ∈ (kb.moduleOf S).items :=
    fun hq hm => mem_moduleOf_items.2 ⟨hq, hm⟩
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, Bool.and_eq_true,
    decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro p hp
    have hp' : kb.Sub p.1 p.2 ∧ p.1 ∈ kb.moduleItemsF S := moduleOf_Sub_iff.1 (by
      simpa [Sub, moduleOf] using hp)
    have h2 : p.2 ∈ kb.moduleItemsF S := moduleItemsF_closed hwf hp'.2 (Or.inl hp'.1)
    exact ⟨hitem (wf_sub hwf hp'.1).1 hp'.2, hitem (wf_sub hwf hp'.1).2 h2⟩
  · intro p hp
    have hp' : kb.Inst p.1 p.2 ∧ p.1 ∈ kb.moduleItemsF S := moduleOf_Inst_iff.1 (by
      simpa [Inst, moduleOf] using hp)
    have h2 : p.2 ∈ kb.moduleItemsF S := moduleItemsF_closed hwf hp'.2 (Or.inr hp'.1)
    exact ⟨hitem (wf_inst hwf hp'.1).1 hp'.2, hitem (wf_inst hwf hp'.1).2 h2⟩
  · intro p hp
    simp only [moduleOf, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨hmem, h1, h2⟩ := hp
    have hwf' : ∀ q ∈ kb.disj, q.1 ∈ kb.items ∧ q.2 ∈ kb.items := by
      simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
      intro q hq; simpa using hwf.2 q hq
    exact ⟨hitem (hwf' p hmem).1 h1, hitem (hwf' p hmem).2 h2⟩

/-! ### Soundness and completeness of the extraction -/

/-- **Soundness for the class hierarchy**: everything the module derives, the base
derives. -/
theorem moduleOf_isSubclassOf_le (hwf : kb.wellFormed = true) {S : List Qid} {a b : Qid}
    (h : (kb.moduleOf S).isSubclassOf a b = true) : kb.isSubclassOf a b = true :=
  (isSubclassOf_iff hwf a b).2
    (((isSubclassOf_iff (moduleOf_wellFormed hwf S) a b).1 h).mono
      (fun _ _ hx => moduleOf_Sub_le hx))

/-- **Soundness for the instance relation.** -/
theorem moduleOf_isInstanceOf_le (hwf : kb.wellFormed = true) {S : List Qid} {a c : Qid}
    (h : (kb.moduleOf S).isInstanceOf a c = true) : kb.isInstanceOf a c = true := by
  obtain ⟨d, hd, hdc⟩ := (isInstanceOf_iff (moduleOf_wellFormed hwf S) a c).1 h
  exact (isInstanceOf_iff hwf a c).2
    ⟨d, moduleOf_Inst_le hd, hdc.mono (fun _ _ hx => moduleOf_Sub_le hx)⟩

/-- A `subclass of` chain starting inside the module stays inside it, hence is a chain
of the module. -/
theorem moduleOf_reflTransGen_sub (hwf : kb.wellFormed = true) {S : List Qid} {a b : Qid}
    (ha : a ∈ kb.moduleItemsF S) (h : Relation.ReflTransGen kb.Sub a b) :
    Relation.ReflTransGen (kb.moduleOf S).Sub a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
      exact ih.tail (moduleOf_Sub_iff.2 ⟨hbc, moduleItemsF_closed_sub hwf ha hab⟩)

/-- **Conservativity for the class hierarchy**: about an item of the module, the module
derives exactly the `subclass of` facts the whole base derives. -/
theorem moduleOf_isSubclassOf (hwf : kb.wellFormed = true) {S : List Qid} {a : Qid}
    (ha : a ∈ kb.moduleItemsF S) (b : Qid) :
    (kb.moduleOf S).isSubclassOf a b = kb.isSubclassOf a b := by
  by_cases h : kb.isSubclassOf a b = true
  · have hpath := (isSubclassOf_iff hwf a b).1 h
    rw [h, (isSubclassOf_iff (moduleOf_wellFormed hwf S) a b).2
      (moduleOf_reflTransGen_sub hwf ha hpath)]
  · simp only [Bool.not_eq_true] at h
    rw [h]
    by_contra hcon
    exact absurd (moduleOf_isSubclassOf_le hwf (by simpa using hcon)) (by simp [h])

/-- **Conservativity for the instance relation.** -/
theorem moduleOf_isInstanceOf (hwf : kb.wellFormed = true) {S : List Qid} {a : Qid}
    (ha : a ∈ kb.moduleItemsF S) (c : Qid) :
    (kb.moduleOf S).isInstanceOf a c = kb.isInstanceOf a c := by
  by_cases h : kb.isInstanceOf a c = true
  · obtain ⟨d, hd, hdc⟩ := (isInstanceOf_iff hwf a c).1 h
    have hdm : d ∈ kb.moduleItemsF S := moduleItemsF_closed hwf ha (Or.inr hd)
    rw [h, (isInstanceOf_iff (moduleOf_wellFormed hwf S) a c).2
      ⟨d, moduleOf_Inst_iff.2 ⟨hd, ha⟩, moduleOf_reflTransGen_sub hwf hdm hdc⟩]
  · simp only [Bool.not_eq_true] at h
    rw [h]
    by_contra hcon
    exact absurd (moduleOf_isInstanceOf_le hwf (by simpa using hcon)) (by simp [h])

/-- **The listed answers agree too**: for an item of the module, the superclasses the
module lists are literally the list the whole base lists. -/
theorem moduleOf_superclassesOfL (hwf : kb.wellFormed = true) {S : List Qid} {a : Qid}
    (ha : a ∈ kb.moduleItemsF S) :
    (kb.moduleOf S).superclassesOfL a = kb.superclassesOfL a := by
  have hmod : (kb.moduleOf S).items = kb.items.filter (fun q => decide (q ∈ kb.moduleItemsF S)) :=
    rfl
  rw [superclassesOfL, superclassesOfL, hmod, List.filter_filter]
  refine List.filter_congr fun b hb => ?_
  by_cases h : kb.isSubclassOf a b = true
  · have hbm : b ∈ kb.moduleItemsF S :=
      moduleItemsF_closed_sub hwf ha ((isSubclassOf_iff hwf a b).1 h)
    simp [h, hbm, moduleOf_isSubclassOf hwf ha b]
  · simp only [Bool.not_eq_true] at h
    simp [h, moduleOf_isSubclassOf hwf ha b]

/-- The same for the classes an item is an instance of. -/
theorem moduleOf_classesOf (hwf : kb.wellFormed = true) {S : List Qid} {a : Qid}
    (ha : a ∈ kb.moduleItemsF S) :
    (kb.moduleOf S).classesOf a = kb.classesOf a := by
  have hmod : (kb.moduleOf S).items = kb.items.filter (fun q => decide (q ∈ kb.moduleItemsF S)) :=
    rfl
  rw [classesOf, classesOf, hmod, List.filter_filter]
  refine List.filter_congr fun c hc => ?_
  by_cases h : kb.isInstanceOf a c = true
  · obtain ⟨d, hd, hdc⟩ := (isInstanceOf_iff hwf a c).1 h
    have hcm : c ∈ kb.moduleItemsF S :=
      moduleItemsF_closed_sub hwf (moduleItemsF_closed hwf ha (Or.inr hd)) hdc
    simp [h, hcm, moduleOf_isInstanceOf hwf ha c]
  · simp only [Bool.not_eq_true] at h
    simp [h, moduleOf_isInstanceOf hwf ha c]

/-! ### Validity is preserved -/

theorem moduleOf_levelsOk (h : kb.levelsOk = true) (S : List Qid) :
    (kb.moduleOf S).levelsOk = true := by
  simp only [levelsOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · intro p hp
    have hp' : kb.Inst p.1 p.2 := moduleOf_Inst_le (by simpa [Inst, moduleOf] using hp)
    simpa using level_inst h hp'
  · intro p hp
    have hp' : kb.Sub p.1 p.2 := moduleOf_Sub_le (by simpa [Sub, moduleOf] using hp)
    have := level_sub h hp'
    simpa [Bool.and_eq_true] using this

theorem moduleOf_acyclic (hwf : kb.wellFormed = true) (hac : kb.acyclic = true) (S : List Qid) :
    (kb.moduleOf S).acyclic = true := by
  rw [acyclic]
  refine List.all_eq_true.2 fun a ha => List.all_eq_true.2 fun b hb => ?_
  obtain ⟨hai, ham⟩ := mem_moduleOf_items.1 ha
  obtain ⟨hbi, hbm⟩ := mem_moduleOf_items.1 hb
  have hkey := List.all_eq_true.1 (List.all_eq_true.1 hac a hai) b hbi
  rw [moduleOf_isSubclassOf hwf ham b, moduleOf_isSubclassOf hwf hbm a]
  exact hkey

theorem moduleOf_disjointOk (hwf : kb.wellFormed = true) (hdj : kb.disjointOk = true)
    (S : List Qid) : (kb.moduleOf S).disjointOk = true := by
  rw [disjointOk]
  refine List.all_eq_true.2 fun p hp => List.all_eq_true.2 fun a ha => ?_
  have hp' : p ∈ kb.disj := List.mem_of_mem_filter hp
  obtain ⟨hai, ham⟩ := mem_moduleOf_items.1 ha
  have hkey := List.all_eq_true.1 (List.all_eq_true.1 hdj p hp') a hai
  rw [moduleOf_isInstanceOf hwf ham p.1, moduleOf_isInstanceOf hwf ham p.2]
  exact hkey

/-- **A module of a validated knowledge base is itself valid**, so it is again an
abstract Wikidata ontology and every theorem of `RequestProject.Core` applies to it. -/
theorem moduleOf_valid (hv : kb.valid = true) (S : List Qid) : (kb.moduleOf S).valid = true := by
  have hwf := valid_wellFormed hv
  simp only [valid, Bool.and_eq_true]
  exact ⟨⟨⟨moduleOf_wellFormed hwf S, moduleOf_levelsOk (valid_levelsOk hv) S⟩,
    moduleOf_acyclic hwf (valid_acyclic hv) S⟩, moduleOf_disjointOk hwf (valid_disjointOk hv) S⟩

/-! ### Structural laws -/

/-- **A base entails its own modules**: extraction never adds knowledge. -/
theorem entails_moduleOf (hwf : kb.wellFormed = true) (S : List Qid) :
    kb.Entails (kb.moduleOf S) = true := by
  simp only [Entails, Bool.and_eq_true, List.all_eq_true]
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · have h : kb.Sub p.1 p.2 := moduleOf_Sub_le (by simpa [Sub] using hp)
    exact (isSubclassOf_iff hwf p.1 p.2).2 (Relation.ReflTransGen.single h)
  · exact isInstanceOf_of_inst (moduleOf_Inst_le (by simpa [Inst] using hp))


/-- Extracting over all the items of a well-formed base returns the base itself
(up to its name). -/
theorem moduleOf_items_self (hwf : kb.wellFormed = true) :
    (kb.moduleOf kb.items).items = kb.items ∧
      (kb.moduleOf kb.items).sub = kb.sub ∧
      (kb.moduleOf kb.items).inst = kb.inst ∧
      (kb.moduleOf kb.items).disj = kb.disj := by
  have hall : ∀ q ∈ kb.items, q ∈ kb.moduleItemsF kb.items := fun q hq =>
    seed_mem_moduleItemsF hq
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact List.filter_eq_self.2 (fun q hq => by simpa using hall q hq)
  · refine List.filter_eq_self.2 (fun p hp => ?_)
    simpa using hall p.1 (wf_sub hwf (show kb.Sub p.1 p.2 from by simpa [Sub] using hp)).1
  · refine List.filter_eq_self.2 (fun p hp => ?_)
    simpa using hall p.1 (wf_inst hwf (show kb.Inst p.1 p.2 from by simpa [Inst] using hp)).1
  · refine List.filter_eq_self.2 (fun p hp => ?_)
    have hwf' : ∀ q ∈ kb.disj, q.1 ∈ kb.items ∧ q.2 ∈ kb.items := by
      simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
      intro q hq; simpa using hwf.2 q hq
    simp [hall p.1 (hwf' p hp).1, hall p.2 (hwf' p hp).2]

/-- **Extraction is idempotent**: the module of a module has the same items. -/
theorem moduleOf_moduleItemsF (hwf : kb.wellFormed = true) {S : List Qid} :
    (kb.moduleOf S).moduleItemsF S = kb.moduleItemsF S := by
  have hwf' := moduleOf_wellFormed hwf S
  ext q
  rw [mem_moduleItemsF_iff hwf', mem_moduleItemsF_iff hwf]
  constructor
  · rintro ⟨s, hs, hpath⟩
    refine ⟨s, hs, ?_⟩
    induction hpath with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih =>
        rcases hbc with h | h
        · exact ih.tail (Or.inl (moduleOf_Sub_le h))
        · exact ih.tail (Or.inr (moduleOf_Inst_le h))
  · rintro ⟨s, hs, hpath⟩
    refine ⟨s, hs, ?_⟩
    have hstart : s ∈ kb.moduleItemsF S := seed_mem_moduleItemsF hs
    induction hpath with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
        have hb := moduleItemsF_closed_path hwf hstart hab
        refine ih.tail ?_
        rcases hbc with h | h
        · exact Or.inl (moduleOf_Sub_iff.2 ⟨h, hb⟩)
        · exact Or.inr (moduleOf_Inst_iff.2 ⟨h, hb⟩)

end KB
end Wikidata
