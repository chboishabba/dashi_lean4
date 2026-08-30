import RequestProject.Merge

/-!
# A knowledge base that carries a description of itself (or of another one)

`KB.selfDescription kb` is the *meta-ontology* of `kb`: an executable knowledge
base whose items are

* `Qid.ont kb.name` — an item denoting the ontology `kb` itself,
* `Qid.about x` for every item `x` of `kb` — the meta-level name of `x`, and
* `Qid.lvl n` — the class of all items of metaclass level `n`,

with the P31 statements `about x` *instance of* `lvl (level x)`,
`lvl n` *instance of* `lvl (n+1)` (the tower of metaclasses), and
`ont kb.name` *instance of* `lvl 0` (an ontology is an individual of the meta level).

The main theorem is `KB.selfDescription_valid`: the meta-description of *any*
knowledge base — including of a meta-description, and in particular of itself —
is a valid Wikidata-style ontology, so it can be reasoned about with the whole
apparatus of `RequestProject.Core`.
-/

namespace Wikidata
namespace KB

/-! ### Lookup helper lemmas -/

theorem le_foldr_max {l : List ℕ} {n : ℕ} (h : n ∈ l) : n ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons a t ih =>
      rcases List.mem_cons.1 h with rfl | h
      · exact le_max_left _ _
      · exact le_trans (ih h) (le_max_right _ _)

theorem lookup_cons_ne {β : Type*} {k q : Qid} {v : β} {l : List (Qid × β)} (h : q ≠ k) :
    List.lookup q ((k, v) :: l) = List.lookup q l := by
  rw [List.lookup_cons]
  rw [beq_eq_false_iff_ne.mpr h]

theorem lookup_cons_self {β : Type*} {k : Qid} {v : β} {l : List (Qid × β)} :
    List.lookup k ((k, v) :: l) = some v := by
  rw [List.lookup_cons, beq_self_eq_true]

theorem lookup_map_about {l : List Qid} {f : Qid → ℕ} {x : Qid} (hx : x ∈ l) :
    List.lookup (Qid.about x) (l.map (fun y => (Qid.about y, f y))) = some (f x) := by
  induction l with
  | nil => cases hx
  | cons y t ih =>
      by_cases hxy : x = y
      · subst hxy; simp
      · rcases List.mem_cons.1 hx with h | h
        · exact absurd h hxy
        · rw [List.map_cons, lookup_cons_ne (by simpa using hxy), ih h]

theorem lookup_map_about_eq_none {l : List Qid} {f : Qid → ℕ} {q : Qid}
    (h : ∀ y, q ≠ Qid.about y) :
    List.lookup q (l.map (fun y => (Qid.about y, f y))) = none := by
  induction l with
  | nil => rfl
  | cons y t ih => rw [List.map_cons, lookup_cons_ne (h y), ih]

theorem lookup_map_lvl {l : List ℕ} {g : ℕ → ℕ} {n : ℕ} (hn : n ∈ l) :
    List.lookup (Qid.lvl n) (l.map (fun k => (Qid.lvl k, g k))) = some (g n) := by
  induction l with
  | nil => cases hn
  | cons m t ih =>
      by_cases hnm : n = m
      · subst hnm; simp
      · rcases List.mem_cons.1 hn with h | h
        · exact absurd h hnm
        · rw [List.map_cons, lookup_cons_ne (by simpa using hnm), ih h]

theorem lookup_map_lvl_eq_none {l : List ℕ} {g : ℕ → ℕ} {q : Qid} (h : ∀ n, q ≠ Qid.lvl n) :
    List.lookup q (l.map (fun k => (Qid.lvl k, g k))) = none := by
  induction l with
  | nil => rfl
  | cons m t ih => rw [List.map_cons, lookup_cons_ne (h m), ih]

/-! ### The construction -/

/-- The greatest metaclass level occurring in the knowledge base. -/
def maxLevel (kb : KB) : ℕ := (kb.items.map kb.levelOf).foldr max 0

theorem levelOf_le_maxLevel (kb : KB) {x : Qid} (hx : x ∈ kb.items) :
    kb.levelOf x ≤ kb.maxLevel :=
  le_foldr_max (List.mem_map_of_mem hx)

/-- The meta-ontology of `kb`: a knowledge base describing `kb`, its items and
their metaclass levels. -/
def selfDescription (kb : KB) : KB where
  name := "meta:" ++ kb.name
  items := (Qid.ont kb.name) ::
    (kb.items.map Qid.about ++ (List.range (kb.maxLevel + 2)).map Qid.lvl)
  levels := (Qid.ont kb.name, 0) ::
    (kb.items.map (fun x => (Qid.about x, kb.levelOf x)) ++
      (List.range (kb.maxLevel + 2)).map (fun n => (Qid.lvl n, n + 1)))
  sub := []
  inst := (Qid.ont kb.name, Qid.lvl 0) ::
    (kb.items.map (fun x => (Qid.about x, Qid.lvl (kb.levelOf x))) ++
      (List.range (kb.maxLevel + 1)).map (fun n => (Qid.lvl n, Qid.lvl (n + 1))))
  disj := []

variable (kb : KB)

@[simp] theorem selfDescription_sub : (kb.selfDescription).sub = [] := rfl
@[simp] theorem selfDescription_disj : (kb.selfDescription).disj = [] := rfl

theorem mem_selfDescription_items_about {x : Qid} (hx : x ∈ kb.items) :
    Qid.about x ∈ (kb.selfDescription).items := by
  simp only [selfDescription, List.mem_cons, List.mem_append, List.mem_map]
  exact Or.inr (Or.inl ⟨x, hx, rfl⟩)

theorem mem_selfDescription_items_lvl {n : ℕ} (hn : n ≤ kb.maxLevel + 1) :
    Qid.lvl n ∈ (kb.selfDescription).items := by
  simp only [selfDescription, List.mem_cons, List.mem_append, List.mem_map, List.mem_range]
  exact Or.inr (Or.inr ⟨n, by omega, rfl⟩)

theorem mem_selfDescription_items_ont : Qid.ont kb.name ∈ (kb.selfDescription).items := by
  simp [selfDescription]

/-! ### Levels in the meta-ontology -/

theorem selfDescription_levels : (kb.selfDescription).levels =
    (Qid.ont kb.name, 0) ::
      (kb.items.map (fun x => (Qid.about x, kb.levelOf x)) ++
        (List.range (kb.maxLevel + 2)).map (fun n => (Qid.lvl n, n + 1))) := rfl

@[simp] theorem selfDescription_levelOf_ont :
    (kb.selfDescription).levelOf (Qid.ont kb.name) = 0 := by
  show (List.lookup (Qid.ont kb.name) (kb.selfDescription).levels).getD 0 = 0
  rw [selfDescription_levels, lookup_cons_self]
  rfl

theorem selfDescription_levelOf_about {x : Qid} (hx : x ∈ kb.items) :
    (kb.selfDescription).levelOf (Qid.about x) = kb.levelOf x := by
  show (List.lookup (Qid.about x) (kb.selfDescription).levels).getD 0 = kb.levelOf x
  rw [selfDescription_levels, lookup_cons_ne (by simp), List.lookup_append,
    lookup_map_about hx]
  rfl

theorem selfDescription_levelOf_lvl {n : ℕ} (hn : n ≤ kb.maxLevel + 1) :
    (kb.selfDescription).levelOf (Qid.lvl n) = n + 1 := by
  show (List.lookup (Qid.lvl n) (kb.selfDescription).levels).getD 0 = n + 1
  rw [selfDescription_levels, lookup_cons_ne (by simp), List.lookup_append,
    lookup_map_about_eq_none (fun y => by simp),
    lookup_map_lvl (l := List.range (kb.maxLevel + 2)) (g := fun k => k + 1)
      (by simp only [List.mem_range]; omega)]
  rfl

/-! ### The meta-ontology is valid -/

theorem selfDescription_wellFormed : (kb.selfDescription).wellFormed = true := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    selfDescription_sub, selfDescription_disj, List.not_mem_nil, false_implies,
    implies_true, and_true, true_and]
  intro p hp
  have hins : (kb.selfDescription).inst = (Qid.ont kb.name, Qid.lvl 0) ::
      (kb.items.map (fun x => (Qid.about x, Qid.lvl (kb.levelOf x))) ++
        (List.range (kb.maxLevel + 1)).map (fun n => (Qid.lvl n, Qid.lvl (n + 1)))) := rfl
  rw [hins, List.mem_cons, List.mem_append, List.mem_map, List.mem_map] at hp
  rcases hp with rfl | ⟨x, hx, rfl⟩ | ⟨n, hn, rfl⟩
  · exact ⟨mem_selfDescription_items_ont kb, mem_selfDescription_items_lvl kb (by omega)⟩
  · exact ⟨mem_selfDescription_items_about kb hx,
      mem_selfDescription_items_lvl kb (le_trans (levelOf_le_maxLevel kb hx) (by omega))⟩
  · rw [List.mem_range] at hn
    exact ⟨mem_selfDescription_items_lvl kb (by omega),
      mem_selfDescription_items_lvl kb (by omega)⟩

theorem selfDescription_levelsOk : (kb.selfDescription).levelsOk = true := by
  simp only [levelsOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq,
    selfDescription_sub, List.not_mem_nil, false_implies, implies_true, and_true]
  intro p hp
  have hins : (kb.selfDescription).inst = (Qid.ont kb.name, Qid.lvl 0) ::
      (kb.items.map (fun x => (Qid.about x, Qid.lvl (kb.levelOf x))) ++
        (List.range (kb.maxLevel + 1)).map (fun n => (Qid.lvl n, Qid.lvl (n + 1)))) := rfl
  rw [hins, List.mem_cons, List.mem_append, List.mem_map, List.mem_map] at hp
  rcases hp with rfl | ⟨x, hx, rfl⟩ | ⟨n, hn, rfl⟩
  · simp [selfDescription_levelOf_lvl kb (n := 0) (by omega)]
  · rw [selfDescription_levelOf_about kb hx,
      selfDescription_levelOf_lvl kb (le_trans (levelOf_le_maxLevel kb hx) (by omega))]
  · rw [List.mem_range] at hn
    rw [selfDescription_levelOf_lvl kb (by omega), selfDescription_levelOf_lvl kb (by omega)]

theorem selfDescription_acyclic : (kb.selfDescription).acyclic = true :=
  acyclic_of_sub_nil rfl

theorem selfDescription_disjointOk : (kb.selfDescription).disjointOk = true := by
  simp [disjointOk, selfDescription]

/-- **Every knowledge base has a valid meta-description.** Since the construction
applies to any knowledge base, it applies to meta-descriptions as well: an
ontology can carry a description of itself and of others, at any depth. -/
theorem selfDescription_valid (kb : KB) : (kb.selfDescription).valid = true := by
  simp only [valid, Bool.and_eq_true]
  exact ⟨⟨⟨selfDescription_wellFormed kb, selfDescription_levelsOk kb⟩,
    selfDescription_acyclic kb⟩, selfDescription_disjointOk kb⟩

/-- The meta-description of a meta-description is again valid. -/
theorem selfDescription_selfDescription_valid (kb : KB) :
    ((kb.selfDescription).selfDescription).valid = true :=
  selfDescription_valid _

/-- The meta-ontology, viewed as an abstract Wikidata ontology. -/
def selfOntology (kb : KB) : Ontology Qid :=
  (kb.selfDescription).toOntology (selfDescription_valid kb)

/-! ### What the meta-ontology says -/

/-- The meta-ontology contains an item denoting the described ontology, and knows
that it is an individual of the meta level. -/
theorem selfDescription_knows_ontology :
    (kb.selfDescription).isInstanceOf (Qid.ont kb.name) (Qid.lvl 0) = true :=
  isInstanceOf_of_inst (by simp [Inst, selfDescription])

/-- The meta-ontology classifies each described item by its metaclass level. -/
theorem selfDescription_knows_item {x : Qid} (hx : x ∈ kb.items) :
    (kb.selfDescription).isInstanceOf (Qid.about x) (Qid.lvl (kb.levelOf x)) = true :=
  isInstanceOf_of_inst (by
    simp only [Inst, selfDescription, List.mem_cons, List.mem_append, List.mem_map]
    exact Or.inr (Or.inl ⟨x, hx, rfl⟩))

/-- The level classes form a tower of metaclasses: `lvl n` is an instance of
`lvl (n+1)`. -/
theorem selfDescription_lvl_tower {n : ℕ} (hn : n ≤ kb.maxLevel) :
    (kb.selfDescription).isInstanceOf (Qid.lvl n) (Qid.lvl (n + 1)) = true :=
  isInstanceOf_of_inst (by
    simp only [Inst, selfDescription, List.mem_cons, List.mem_append, List.mem_map,
      List.mem_range]
    exact Or.inr (Or.inr ⟨n, by omega, rfl⟩))

/-- In the meta-ontology, the class of level-`n` items really does sit at level
`n+1`. -/
theorem selfOntology_level_lvl {n : ℕ} (hn : n ≤ kb.maxLevel + 1) :
    (kb.selfOntology).level (Qid.lvl n) = n + 1 :=
  selfDescription_levelOf_lvl kb hn

/-- In the meta-ontology, the class of items of level `level x` is a genuine
metaclass: it has an instance which itself has instances. -/
theorem selfDescription_lvl_isMetaclass {x : Qid} (hx : x ∈ kb.items) :
    (kb.selfDescription).isMetaclassB (Qid.lvl (kb.levelOf x + 1)) = true :=
  isMetaclassB_eq_true
    (mem_selfDescription_items_lvl kb (le_trans (levelOf_le_maxLevel kb hx) (by omega)))
    (selfDescription_lvl_tower kb (levelOf_le_maxLevel kb hx))
    (hasInstanceB_eq_true (mem_selfDescription_items_about kb hx)
      (selfDescription_knows_item kb hx))

/-- The same fact in the abstract model: `lvl (level x + 1)` is a metaclass of the
meta-ontology, hence sits at level at least `2`. -/
theorem selfOntology_isMetaclass_lvl {x : Qid} (hx : x ∈ kb.items) :
    (kb.selfOntology).IsMetaclass (Qid.lvl (kb.levelOf x + 1)) := by
  refine ⟨Qid.lvl (kb.levelOf x), ?_, Qid.about x, ?_⟩
  · exact (isInstanceOf_iff_instanceOf (selfDescription_valid kb) _ _).1
      (selfDescription_lvl_tower kb (levelOf_le_maxLevel kb hx))
  · exact (isInstanceOf_iff_instanceOf (selfDescription_valid kb) _ _).1
      (selfDescription_knows_item kb hx)

end KB
end Wikidata
