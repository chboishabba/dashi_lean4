import RequestProject.Engine

/-!
# The mereological layer: `part of` (P361) and `has parts of the class` (P2670)

*Wikidata:WikiProject Ontology* insists that the **meronomy** (the part–whole
hierarchy, built from `part of`, P361, and its inverse `has part(s)`, P527) is a
different hierarchy from the **taxonomy** (`subclass of`, P279): a wheel is *part of*
a bicycle but it is not a *kind of* bicycle, and being an instance of a class one of
whose members is a part of something does not make you a part of anything.

This file adds that layer to the executable knowledge base of
`RequestProject.Engine`. An `MKB` is a `KB` together with

* direct `part of` statements `(part, whole)`, and
* `has parts of the class` (P2670) declarations `(whole class, part class)`: every
  instance of the first class is expected to have a proper part which is an
  instance of the second.

Everything is computable — `MKB.isPartOfB`, `MKB.isProperPartOfB`,
`MKB.overlapsB`, `MKB.partCompleteB` — and certified: for a well-formed layer
`isPartOfB` decides the reflexive–transitive closure of the asserted P361
statements (`MKB.isPartOfB_iff`).

The main results are:

* part-of is a **partial order** on a valid layer: reflexive, transitive and
  antisymmetric, so proper part-of is a strict order (`MKB.properPartOf_trans`,
  `MKB.properPartOf_asymm`);
* the mereology is **well founded** (`MKB.properWhole_wf`): the number of wholes
  above an item strictly decreases as one moves up the part hierarchy, so one may
  do induction from the parts upwards;
* the meronomy is **not** the taxonomy: a validated layer never asserts a part
  statement between a class and one of its superclasses or classes
  (`MKB.part_not_subclass`, `MKB.part_not_instance`), and part-of is **not
  inherited** through `instance of` — a worked counterexample is decided
  (`MKB.partOf_not_inherited`);
* overlap behaves as it should (symmetric, monotone along part-of);
* the P2670 layer: expectations are **inherited downwards** along `subclass of`
  (`MKB.mem_expectedPartClasses_of_subclass`), a base passing the completeness
  check really exhibits the required parts (`MKB.partComplete_exhibits`), and
  asserting further part statements never destroys completeness
  (`MKB.partCompleteB_mono`).
-/

namespace Wikidata

/-- A finite, executable **mereological layer** over a knowledge base: the `part of`
(P361) statements and the `has parts of the class` (P2670) declarations. -/
structure MKB where
  /-- The underlying item ontology (taxonomy). -/
  base : KB
  /-- Direct `part of` (P361) statements, written `(part, whole)`. -/
  parts : List (Qid × Qid) := []
  /-- `has parts of the class` (P2670) declarations, written
  `(whole class, part class)`. -/
  partClasses : List (Qid × Qid) := []
deriving Repr, DecidableEq, Inhabited

namespace MKB

variable (m : MKB)

/-! ### The computational engine -/

/-- The items an item is a direct part of. -/
def wholesL (q : Qid) : List Qid := (m.parts.filter (fun r => r.1 == q)).map Prod.snd

/-- The items an item is a direct part of, as a `Finset`. -/
def wholes (q : Qid) : Finset Qid := (m.wholesL q).toFinset

/-- All wholes above an item, computed by saturating the P361 graph. -/
def wholeClosure (q : Qid) : Finset Qid := Reach.reach m.wholes m.base.allF q

/-- Decides (reflexive) `part of`: `a` is `b`, or a part of a part of … of `b`. -/
def isPartOfB (a b : Qid) : Bool := b ∈ m.wholeClosure a

/-- Decides *proper* part-of. -/
def isProperPartOfB (a b : Qid) : Bool := m.isPartOfB a b && a != b

/-- The proper parts of an item, among the items. -/
def properPartsOfL (b : Qid) : List Qid := m.base.items.filter (fun a => m.isProperPartOfB a b)

/-- The proper wholes of an item, among the items. -/
def wholesOfL (a : Qid) : List Qid := m.base.items.filter (fun b => m.isProperPartOfB a b)

/-- Two items **overlap** when some item is a part of both. -/
def overlapsB (a b : Qid) : Bool :=
  m.base.items.any (fun c => m.isPartOfB c a && m.isPartOfB c b)

/-- The number of wholes above an item (itself included): the measure that makes the
part hierarchy well founded. -/
def mereoHeight (a : Qid) : ℕ := (m.wholeClosure a).card

/-! ### The validator -/

/-- All mereological statements mention declared items. -/
def mWellFormed : Bool :=
  m.base.wellFormed &&
  m.parts.all (fun r => r.1 ∈ m.base.items && r.2 ∈ m.base.items) &&
  m.partClasses.all (fun r => r.1 ∈ m.base.items && r.2 ∈ m.base.items)

/-- The part hierarchy has no cycles. -/
def mAcyclic : Bool :=
  m.base.items.all (fun a => m.base.items.all
    (fun b => !(m.isPartOfB a b && m.isPartOfB b a) || a == b))

/-- The meronomy is not the taxonomy: no asserted part statement is also a
`subclass of` or an `instance of` fact. -/
def noClassConfusion : Bool :=
  m.parts.all (fun r => !m.base.isSubclassOf r.1 r.2 && !m.base.isInstanceOf r.1 r.2)

/-- The full validity check for a mereological layer. -/
def mValid : Bool := m.base.valid && m.mWellFormed && m.mAcyclic && m.noClassConfusion

/-! ### Semantics -/

/-- The asserted `part of` statements, as a relation. -/
def Part (a b : Qid) : Prop := (a, b) ∈ m.parts

/-- Derived `part of`: the reflexive–transitive closure of the asserted statements. -/
def PartOf (a b : Qid) : Prop := Relation.ReflTransGen m.Part a b

variable {m}

theorem mem_wholes {a b : Qid} : b ∈ m.wholes a ↔ m.Part a b := by
  simp [wholes, wholesL, Part, List.mem_filter, List.mem_map]

theorem succ_eq_part (m : MKB) : (fun u v => v ∈ m.wholes u) = m.Part := by
  funext u v; exact propext mem_wholes

theorem mwf_base (h : m.mWellFormed = true) : m.base.wellFormed = true := by
  simp only [mWellFormed, Bool.and_eq_true] at h; tauto

/-- Both endpoints of a part statement of a well-formed layer are items. -/
theorem mwf_part (h : m.mWellFormed = true) {a b : Qid} (hab : m.Part a b) :
    a ∈ m.base.items ∧ b ∈ m.base.items := by
  simp only [mWellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  simpa using h.1.2 (a, b) hab

/-- Both endpoints of a P2670 declaration of a well-formed layer are items. -/
theorem mwf_partClass (h : m.mWellFormed = true) {c d : Qid} (hcd : (c, d) ∈ m.partClasses) :
    c ∈ m.base.items ∧ d ∈ m.base.items := by
  simp only [mWellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  simpa using h.2 (c, d) hcd

theorem wholes_subset_allF (h : m.mWellFormed = true) (y : Qid) : m.wholes y ⊆ m.base.allF := by
  intro b hb
  simpa [KB.allF] using (mwf_part h (mem_wholes.1 hb)).2

theorem wholes_eq_empty_of_not_mem (h : m.mWellFormed = true) {a : Qid}
    (ha : a ∉ m.base.items) : m.wholes a = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.2 fun b hb => ?_
  exact ha (mwf_part h (mem_wholes.1 hb)).1

/-- **Certified part-of computation**: in a well-formed layer the Boolean check
`isPartOfB` decides the reflexive–transitive closure of the asserted P361
statements. -/
theorem isPartOfB_iff (h : m.mWellFormed = true) (a b : Qid) :
    m.isPartOfB a b = true ↔ m.PartOf a b := by
  have hcl := Reach.mem_reach_iff_of_closed m.wholes (wholes_subset_allF h)
    (fun y hy => wholes_eq_empty_of_not_mem h (by simpa [KB.allF] using hy)) a b
  rw [succ_eq_part] at hcl
  simpa [isPartOfB, wholeClosure, PartOf] using hcl

theorem isPartOfB_refl (m : MKB) (a : Qid) : m.isPartOfB a a = true := by
  simpa [isPartOfB, wholeClosure] using Reach.mem_reach_self m.wholes m.base.allF a

theorem isPartOfB_of_part (h : m.mWellFormed = true) {a b : Qid} (hab : m.Part a b) :
    m.isPartOfB a b = true :=
  (isPartOfB_iff h a b).2 (Relation.ReflTransGen.single hab)

theorem isPartOfB_trans (h : m.mWellFormed = true) {a b c : Qid}
    (hab : m.isPartOfB a b = true) (hbc : m.isPartOfB b c = true) : m.isPartOfB a c = true :=
  (isPartOfB_iff h a c).2 (((isPartOfB_iff h a b).1 hab).trans ((isPartOfB_iff h b c).1 hbc))

/-- Everything above an item of the base is again an item of the base. -/
theorem mem_items_of_isPartOfB (h : m.mWellFormed = true) {a b : Qid}
    (ha : a ∈ m.base.items) (hab : m.isPartOfB a b = true) : b ∈ m.base.items := by
  have := (isPartOfB_iff h a b).1 hab
  induction this with
  | refl => exact ha
  | tail _ hstep _ => exact (mwf_part h hstep).2

/-- A proper part of an item is itself an item. -/
theorem mem_items_of_isProperPartOfB (h : m.mWellFormed = true) {a b : Qid}
    (hab : m.isProperPartOfB a b = true) : a ∈ m.base.items := by
  simp only [isProperPartOfB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab
  by_contra ha
  have : m.wholes a = ∅ := wholes_eq_empty_of_not_mem h ha
  have hcl : m.PartOf a b := (isPartOfB_iff h a b).1 hab.1
  rcases Relation.reflTransGen_iff_eq_or_transGen.1 hcl with rfl | hgen
  · exact hab.2 rfl
  · exact ha (mwf_part h (Relation.TransGen.head'_iff.1 hgen).choose_spec.1).1

/-! ### Part-of is a partial order, and the mereology is well founded -/

/-- Antisymmetry of part-of on a layer whose part hierarchy is acyclic. -/
theorem isPartOfB_antisymm (h : m.mWellFormed = true) (hac : m.mAcyclic = true) {a b : Qid}
    (hab : m.isPartOfB a b = true) (hba : m.isPartOfB b a = true) : a = b := by
  by_cases hne : a = b
  · exact hne
  · exfalso
    have ha : a ∈ m.base.items := mem_items_of_isProperPartOfB h (by
      simp only [isProperPartOfB, Bool.and_eq_true, bne_iff_ne, ne_eq]
      exact ⟨hab, hne⟩)
    have hb : b ∈ m.base.items := mem_items_of_isPartOfB h ha hab
    simp only [mAcyclic, List.all_eq_true] at hac
    have := hac a ha b hb
    simp [hab, hba, hne] at this

theorem properPartOf_irrefl (m : MKB) (a : Qid) : m.isProperPartOfB a a = false := by
  simp [isProperPartOfB]

/-- Proper part-of is asymmetric on a valid layer. -/
theorem properPartOf_asymm (h : m.mWellFormed = true) (hac : m.mAcyclic = true) {a b : Qid}
    (hab : m.isProperPartOfB a b = true) (hba : m.isProperPartOfB b a = true) : False := by
  simp only [isProperPartOfB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab hba
  exact hab.2 (isPartOfB_antisymm h hac hab.1 hba.1)

/-- Proper part-of is transitive on a valid layer. -/
theorem properPartOf_trans (h : m.mWellFormed = true) (hac : m.mAcyclic = true) {a b c : Qid}
    (hab : m.isProperPartOfB a b = true) (hbc : m.isProperPartOfB b c = true) :
    m.isProperPartOfB a c = true := by
  simp only [isProperPartOfB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab hbc ⊢
  refine ⟨isPartOfB_trans h hab.1 hbc.1, ?_⟩
  rintro rfl
  exact hbc.2 (isPartOfB_antisymm h hac hbc.1 hab.1)

theorem wholeClosure_subset (h : m.mWellFormed = true) {a b : Qid}
    (hab : m.isPartOfB a b = true) : m.wholeClosure b ⊆ m.wholeClosure a := by
  intro c hc
  have hbc : m.isPartOfB b c = true := by simpa [isPartOfB] using hc
  simpa [isPartOfB] using isPartOfB_trans h hab hbc

/-- **The part hierarchy strictly decreases the mereological height**: an item has
strictly more wholes above it than any of its proper wholes. -/
theorem mereoHeight_lt (h : m.mWellFormed = true) (hac : m.mAcyclic = true) {a b : Qid}
    (hab : m.isProperPartOfB a b = true) : m.mereoHeight b < m.mereoHeight a := by
  have hab' : m.isPartOfB a b = true := by
    simp only [isProperPartOfB, Bool.and_eq_true] at hab
    exact hab.1
  refine Finset.card_lt_card ⟨wholeClosure_subset h hab', fun hsub => ?_⟩
  have ha : a ∈ m.wholeClosure a := by
    simpa [isPartOfB] using isPartOfB_refl m a
  have hba : m.isPartOfB b a = true := by simpa [isPartOfB] using hsub ha
  simp only [isProperPartOfB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab
  exact hab.2 (isPartOfB_antisymm h hac hab' hba)

/-- **The mereology is well founded**: there is no infinite chain of proper wholes,
so one may reason by induction from the parts upwards. -/
theorem properWhole_wf (h : m.mWellFormed = true) (hac : m.mAcyclic = true) :
    WellFounded (fun b a : Qid => m.isProperPartOfB a b = true) := by
  refine Subrelation.wf (r := InvImage (· < ·) m.mereoHeight) ?_ (InvImage.wf _ Nat.lt_wfRel.wf)
  intro b a hab
  exact mereoHeight_lt h hac hab

/-- No item is a proper part of itself, even through a chain of part statements. -/
theorem not_transGen_properPartOf_self (h : m.mWellFormed = true) (hac : m.mAcyclic = true)
    (a : Qid) : ¬ Relation.TransGen (fun x y : Qid => m.isProperPartOfB x y = true) a a := by
  intro hgen
  have key : ∀ {x y : Qid},
      Relation.TransGen (fun x y : Qid => m.isProperPartOfB x y = true) x y →
      m.isProperPartOfB x y = true := by
    intro x y hxy
    induction hxy with
    | single hstep => exact hstep
    | tail _ hstep ih => exact properPartOf_trans h hac ih hstep
  have := key hgen
  simp [properPartOf_irrefl] at this

/-! ### Overlap -/

theorem overlapsB_comm (m : MKB) (a b : Qid) : m.overlapsB a b = m.overlapsB b a := by
  rw [Bool.eq_iff_iff]
  simp only [overlapsB, List.any_eq_true, Bool.and_eq_true]
  exact ⟨fun ⟨c, hc, h1, h2⟩ => ⟨c, hc, h2, h1⟩, fun ⟨c, hc, h1, h2⟩ => ⟨c, hc, h2, h1⟩⟩

/-- Every item overlaps itself. -/
theorem overlapsB_self {a : Qid} (ha : a ∈ m.base.items) : m.overlapsB a a = true := by
  simp only [overlapsB, List.any_eq_true, Bool.and_eq_true]
  exact ⟨a, ha, isPartOfB_refl m a, isPartOfB_refl m a⟩

/-- Overlap is monotone along part-of: whatever overlaps a part overlaps the whole. -/
theorem overlapsB_mono (h : m.mWellFormed = true) {a b c : Qid}
    (hab : m.isPartOfB a b = true) (hca : m.overlapsB c a = true) : m.overlapsB c b = true := by
  simp only [overlapsB, List.any_eq_true, Bool.and_eq_true] at hca ⊢
  obtain ⟨d, hd, hdc, hda⟩ := hca
  exact ⟨d, hd, hdc, isPartOfB_trans h hda hab⟩

/-- A part always overlaps its whole. -/
theorem overlapsB_of_isPartOfB {a b : Qid} (ha : a ∈ m.base.items)
    (hab : m.isPartOfB a b = true) : m.overlapsB a b = true := by
  simp only [overlapsB, List.any_eq_true, Bool.and_eq_true]
  exact ⟨a, ha, isPartOfB_refl m a, hab⟩

/-! ### The meronomy is not the taxonomy -/

/-- A validated layer never asserts that a class is a part of one of its
superclasses. -/
theorem part_not_subclass (h : m.noClassConfusion = true) {a b : Qid} (hab : m.Part a b) :
    m.base.isSubclassOf a b = false := by
  simp only [noClassConfusion, List.all_eq_true, Bool.and_eq_true] at h
  simpa using (h (a, b) hab).1

/-- A validated layer never asserts that an item is a part of a class it instantiates. -/
theorem part_not_instance (h : m.noClassConfusion = true) {a b : Qid} (hab : m.Part a b) :
    m.base.isInstanceOf a b = false := by
  simp only [noClassConfusion, List.all_eq_true, Bool.and_eq_true] at h
  simpa using (h (a, b) hab).2

/-! ### `has parts of the class` (P2670) -/

variable (m)

/-- The part classes expected of an item: those declared by P2670 on any class it is
an instance of. -/
def expectedPartClassesL (a : Qid) : List Qid :=
  (m.partClasses.filter (fun r => m.base.isInstanceOf a r.1)).map Prod.snd

/-- Decides whether an item has a proper part which is an instance of a given class. -/
def hasPartOfClassB (a d : Qid) : Bool :=
  m.base.items.any (fun p => m.isProperPartOfB p a && m.base.isInstanceOf p d)

/-- The part classes an item is expected to have a part of, but has not. -/
def missingPartClassesL (a : Qid) : List Qid :=
  (m.expectedPartClassesL a).filter (fun d => !m.hasPartOfClassB a d)

/-- An item is *part complete* when it exhibits a part for every P2670 expectation. -/
def partCompleteB (a : Qid) : Bool := (m.missingPartClassesL a).isEmpty

/-- The whole base is part complete. -/
def mComplete : Bool := m.base.items.all (fun a => m.partCompleteB a)

variable {m}

theorem mem_expectedPartClassesL {a d : Qid} :
    d ∈ m.expectedPartClassesL a ↔
      ∃ c, (c, d) ∈ m.partClasses ∧ m.base.isInstanceOf a c = true := by
  simp only [expectedPartClassesL, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨c, d'⟩, ⟨hmem, hinst⟩, rfl⟩; exact ⟨c, hmem, by simpa using hinst⟩
  · rintro ⟨c, hmem, hinst⟩; exact ⟨(c, d), ⟨hmem, by simpa using hinst⟩, rfl⟩

/-- **P2670 expectations are inherited downwards**: an instance of a subclass is held
to the part profile declared on every class above it. -/
theorem mem_expectedPartClasses_of_subclass (hwf : m.base.wellFormed = true) {a c c' d : Qid}
    (hac : m.base.isInstanceOf a c = true) (hcc' : m.base.isSubclassOf c c' = true)
    (hd : (c', d) ∈ m.partClasses) : d ∈ m.expectedPartClassesL a :=
  mem_expectedPartClassesL.2 ⟨c', hd, KB.isInstanceOf_trans_subclass hwf hac hcc'⟩

theorem partCompleteB_iff {a : Qid} :
    m.partCompleteB a = true ↔ ∀ d ∈ m.expectedPartClassesL a, m.hasPartOfClassB a d = true := by
  simp [partCompleteB, missingPartClassesL, List.isEmpty_iff, List.filter_eq_nil_iff]

theorem hasPartOfClassB_iff {a d : Qid} :
    m.hasPartOfClassB a d = true ↔
      ∃ p ∈ m.base.items, m.isProperPartOfB p a = true ∧ m.base.isInstanceOf p d = true := by
  simp [hasPartOfClassB, List.any_eq_true]

/-- **A part complete item really exhibits the required parts**, for every part class
declared on any of its (possibly indirect) classes. -/
theorem partComplete_exhibits (hwf : m.base.wellFormed = true) {a c c' d : Qid}
    (hcomp : m.partCompleteB a = true) (hac : m.base.isInstanceOf a c = true)
    (hcc' : m.base.isSubclassOf c c' = true) (hd : (c', d) ∈ m.partClasses) :
    ∃ p ∈ m.base.items, m.isProperPartOfB p a = true ∧ m.base.isInstanceOf p d = true :=
  hasPartOfClassB_iff.1
    (partCompleteB_iff.1 hcomp d (mem_expectedPartClasses_of_subclass hwf hac hcc' hd))

/-! ### Monotonicity: asserting more parts never destroys completeness -/

/-- Adding a part statement only adds derived part facts. -/
theorem isPartOfB_mono {r : Qid × Qid} (h : m.mWellFormed = true)
    (h' : { m with parts := r :: m.parts }.mWellFormed = true) {a b : Qid}
    (hab : m.isPartOfB a b = true) : { m with parts := r :: m.parts }.isPartOfB a b = true := by
  refine (isPartOfB_iff h' a b).2 ?_
  refine Relation.ReflTransGen.mono ?_ ((isPartOfB_iff h a b).1 hab)
  intro x y hxy
  exact List.mem_cons_of_mem _ hxy

theorem isProperPartOfB_mono {r : Qid × Qid} (h : m.mWellFormed = true)
    (h' : { m with parts := r :: m.parts }.mWellFormed = true) {a b : Qid}
    (hab : m.isProperPartOfB a b = true) :
    { m with parts := r :: m.parts }.isProperPartOfB a b = true := by
  simp only [isProperPartOfB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hab ⊢
  exact ⟨isPartOfB_mono h h' hab.1, hab.2⟩

/-- **Asserting further part statements preserves part completeness.** -/
theorem partCompleteB_mono {r : Qid × Qid} (h : m.mWellFormed = true)
    (h' : { m with parts := r :: m.parts }.mWellFormed = true) {a : Qid}
    (hcomp : m.partCompleteB a = true) :
    { m with parts := r :: m.parts }.partCompleteB a = true := by
  refine partCompleteB_iff.2 fun d hd => ?_
  have hd' : d ∈ m.expectedPartClassesL a := by
    simpa [expectedPartClassesL] using hd
  obtain ⟨p, hp, hpa, hpd⟩ := hasPartOfClassB_iff.1 (partCompleteB_iff.1 hcomp d hd')
  exact hasPartOfClassB_iff.2 ⟨p, hp, isProperPartOfB_mono h h' hpa, hpd⟩

/-! ### Principles of classical mereology

Which of the classical mereological principles does a Wikidata-style part hierarchy
satisfy? Being finite and acyclic it is necessarily **atomistic** — every item is built
from items without proper parts. The **supplementation** and **extensionality**
principles, on the other hand, are not consequences of the data model: they are extra
conditions on a base, checked here and refuted by a fragment below. -/

variable (m)

/-- The proper parts of an item, as a `Finset`. -/
def properPartsF (a : Qid) : Finset Qid :=
  m.base.allF.filter (fun u => m.isProperPartOfB u a = true)

/-- The number of proper parts of an item: the measure that makes descent into the
parts terminate. -/
def mereoDepth (a : Qid) : ℕ := (m.properPartsF a).card

/-- An **atom** is an item with no proper parts. -/
def isAtomB (a : Qid) : Bool := (m.properPartsOfL a).isEmpty

/-- **Weak supplementation**: whenever an item has a proper part, it has a further part
not overlapping it. -/
def weakSupplementationB : Bool :=
  m.base.items.all (fun b => m.base.items.all (fun a =>
    !m.isProperPartOfB a b ||
      m.base.items.any (fun c => m.isPartOfB c b && !m.overlapsB c a)))

/-- **Extensionality of parthood**: two items with the same nonempty collection of
proper parts are the same item. -/
def extensionalB : Bool :=
  m.base.items.all (fun a => m.base.items.all (fun b =>
    !((a != b) && !(m.properPartsOfL a).isEmpty &&
      (m.properPartsOfL a == m.properPartsOfL b))))

variable {m}

theorem mem_properPartsF {a u : Qid} :
    u ∈ m.properPartsF a ↔ u ∈ m.base.items ∧ m.isProperPartOfB u a = true := by
  simp [properPartsF, KB.allF]

theorem isAtomB_iff {a : Qid} :
    m.isAtomB a = true ↔ ∀ u ∈ m.base.items, m.isProperPartOfB u a = false := by
  simp only [isAtomB, properPartsOfL, List.isEmpty_iff, List.filter_eq_nil_iff,
    Bool.not_eq_true]

theorem not_isAtomB_iff {a : Qid} :
    m.isAtomB a = false ↔ ∃ u ∈ m.base.items, m.isProperPartOfB u a = true := by
  rw [← Bool.not_eq_true, isAtomB_iff]
  push_neg
  simp

/-- Descending into a proper part strictly decreases the number of proper parts. -/
theorem mereoDepth_lt (h : m.mWellFormed = true) (hac : m.mAcyclic = true) {p a : Qid}
    (hpa : m.isProperPartOfB p a = true) : m.mereoDepth p < m.mereoDepth a := by
  have hp : p ∈ m.base.items := mem_items_of_isProperPartOfB h hpa
  refine Finset.card_lt_card ⟨fun u hu => ?_, fun hsub => ?_⟩
  · obtain ⟨hu1, hu2⟩ := mem_properPartsF.1 hu
    exact mem_properPartsF.2 ⟨hu1, properPartOf_trans h hac hu2 hpa⟩
  · have : p ∈ m.properPartsF p := hsub (mem_properPartsF.2 ⟨hp, hpa⟩)
    have := (mem_properPartsF.1 this).2
    simp [properPartOf_irrefl] at this

/-- **Every item is built from atoms**: in a valid layer each item has a part which has
no proper parts of its own. -/
theorem exists_atom_part (h : m.mWellFormed = true) (hac : m.mAcyclic = true) :
    ∀ a : Qid, a ∈ m.base.items →
      ∃ p ∈ m.base.items, m.isPartOfB p a = true ∧ m.isAtomB p = true := by
  intro a
  induction hd : m.mereoDepth a using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    intro ha
    by_cases hat : m.isAtomB a = true
    · exact ⟨a, ha, isPartOfB_refl m a, hat⟩
    · obtain ⟨u, hu, hua⟩ := not_isAtomB_iff.1 (Bool.not_eq_true _ ▸ hat)
      have hlt : m.mereoDepth u < n := hd ▸ mereoDepth_lt h hac hua
      obtain ⟨p, hp, hpu, hatp⟩ := ih (m.mereoDepth u) hlt u rfl hu
      refine ⟨p, hp, isPartOfB_trans h hpu ?_, hatp⟩
      simp only [isProperPartOfB, Bool.and_eq_true] at hua
      exact hua.1

/-- Soundness of the weak supplementation check. -/
theorem exists_disjoint_part_of_weakSupplementation (hws : m.weakSupplementationB = true)
    {a b : Qid} (ha : a ∈ m.base.items) (hb : b ∈ m.base.items)
    (hab : m.isProperPartOfB a b = true) :
    ∃ c ∈ m.base.items, m.isPartOfB c b = true ∧ m.overlapsB c a = false := by
  simp only [weakSupplementationB, List.all_eq_true] at hws
  have := hws b hb a ha
  simp only [hab, Bool.not_true, Bool.false_or, List.any_eq_true, Bool.and_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true] at this
  obtain ⟨c, hc, h1, h2⟩ := this
  exact ⟨c, hc, h1, h2⟩

/-- Soundness of the extensionality check. -/
theorem eq_of_extensional (hex : m.extensionalB = true) {a b : Qid}
    (ha : a ∈ m.base.items) (hb : b ∈ m.base.items)
    (hne : (m.properPartsOfL a).isEmpty = false)
    (heq : m.properPartsOfL a = m.properPartsOfL b) : a = b := by
  simp only [extensionalB, List.all_eq_true] at hex
  have := hex a ha b hb
  simp only [heq, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.and_eq_false_iff,
    bne_eq_false_iff_eq, beq_self_eq_true, Bool.not_false, Bool.and_true] at this
  rcases this with h | h
  · exact h
  · rw [heq] at hne
    simp [h] at hne

end MKB

/-! ## A worked fragment

A bicycle (`Q11442`) with a wheel (`Q446`) and a saddle (`Q1444`); the wheel has a
rim (`Q1076486`) as a part. `bicycle` is declared to have parts of the class
`wheel`, and the concrete bicycle `b1` instantiates it. The classes sit at level 1,
the concrete objects at level 0. -/

/-- The taxonomy of the worked fragment. -/
def bikeBase : KB where
  name := "bikes"
  items := [Qid.wd "Q11442", Qid.wd "Q446", Qid.wd "Q1444", Qid.wd "Q1076486",
            Qid.wd "b1", Qid.wd "w1", Qid.wd "s1", Qid.wd "r1"]
  levels := [(Qid.wd "Q11442", 1), (Qid.wd "Q446", 1), (Qid.wd "Q1444", 1),
             (Qid.wd "Q1076486", 1)]
  inst := [(Qid.wd "b1", Qid.wd "Q11442"), (Qid.wd "w1", Qid.wd "Q446"),
           (Qid.wd "s1", Qid.wd "Q1444"), (Qid.wd "r1", Qid.wd "Q1076486")]

/-- The mereological layer of the worked fragment. -/
def bikeMKB : MKB where
  base := bikeBase
  parts := [(Qid.wd "w1", Qid.wd "b1"), (Qid.wd "s1", Qid.wd "b1"),
            (Qid.wd "r1", Qid.wd "w1")]
  partClasses := [(Qid.wd "Q11442", Qid.wd "Q446")]

theorem bikeMKB_valid : bikeMKB.mValid = true := by decide

theorem bikeMKB_wellFormed : bikeMKB.mWellFormed = true := by decide

theorem bikeMKB_acyclic : bikeMKB.mAcyclic = true := by decide

/-- The rim is a part of the bicycle, by transitivity through the wheel. -/
theorem rim_part_of_bike :
    bikeMKB.isProperPartOfB (Qid.wd "r1") (Qid.wd "b1") = true := by decide

/-- The bicycle is not a part of the rim. -/
theorem bike_not_part_of_rim :
    bikeMKB.isPartOfB (Qid.wd "b1") (Qid.wd "r1") = false := by decide

/-- The wheel and the bicycle overlap; the wheel and the saddle do not. -/
theorem wheel_overlaps_bike :
    bikeMKB.overlapsB (Qid.wd "w1") (Qid.wd "b1") = true := by decide

theorem wheel_not_overlaps_saddle :
    bikeMKB.overlapsB (Qid.wd "w1") (Qid.wd "s1") = false := by decide

/-- The bicycle satisfies its `has parts of the class wheel` declaration. -/
theorem bike_partComplete : bikeMKB.partCompleteB (Qid.wd "b1") = true := by decide

/-- The whole fragment is part complete. -/
theorem bikeMKB_complete : bikeMKB.mComplete = true := by decide

/-- Dropping the wheel loses completeness: the bicycle then has no part of the class
`wheel`. -/
theorem bike_incomplete_without_wheel :
    { bikeMKB with parts := [(Qid.wd "s1", Qid.wd "b1")] }.mComplete = false := by decide

/-- **Part-of is not inherited through `instance of`.** In the fragment `w1` is an
instance of the class `wheel` and a part of `b1`, but the class `wheel` itself is not
a part of `b1`, and `r1` — an instance of `rim`, a class whose instance `r1` is a
part of `w1` — is not a part of the *class* `wheel`. -/
theorem partOf_not_inherited :
    bikeMKB.isPartOfB (Qid.wd "Q446") (Qid.wd "b1") = false ∧
    bikeMKB.isPartOfB (Qid.wd "r1") (Qid.wd "Q446") = false := by decide

/-- Nor is `part of` confused with `subclass of` in the fragment: the wheel is a part
of the bicycle but no subclass relation holds between the two classes. -/
theorem wheel_not_subclass_bike :
    bikeBase.isSubclassOf (Qid.wd "Q446") (Qid.wd "Q11442") = false := by decide

/-! ### Atoms, supplementation and extensionality in the fragment -/

/-- The rim and the saddle are atoms of the fragment; the bicycle is not. -/
theorem bike_atoms :
    bikeMKB.isAtomB (Qid.wd "r1") = true ∧ bikeMKB.isAtomB (Qid.wd "s1") = true ∧
    bikeMKB.isAtomB (Qid.wd "b1") = false := by decide

/-- **Weak supplementation fails on the fragment**, and for a reason familiar from real
data: the only recorded part of the wheel is the rim, so the wheel has no part disjoint
from its rim. Supplementation is a property of *complete* data, not of the data model. -/
theorem bike_not_weakSupplementation : bikeMKB.weakSupplementationB = false := by decide

/-- The fragment with a tyre `t1` added as a second part of the wheel. -/
def bikeMKB' : MKB :=
  { bikeMKB with
    base := { bikeMKB.base with items := bikeMKB.base.items ++ [Qid.wd "t1"] },
    parts := bikeMKB.parts ++ [(Qid.wd "t1", Qid.wd "w1")] }

/-- Once the wheel has two recorded parts the fragment is valid, weakly supplemented,
extensional and still part complete. -/
theorem bikeMKB'_supplemented :
    bikeMKB'.mValid = true ∧ bikeMKB'.weakSupplementationB = true ∧
    bikeMKB'.extensionalB = true ∧ bikeMKB'.mComplete = true := by decide

/-- Two distinct wholes recorded with exactly the same part: extensionality of parthood
is **not** a consequence of the Wikidata data model. -/
def twinsMKB : MKB where
  base :=
    { name := "twins"
      items := [Qid.wd "w1", Qid.wd "w2", Qid.wd "p1"] }
  parts := [(Qid.wd "p1", Qid.wd "w1"), (Qid.wd "p1", Qid.wd "w2")]

theorem twinsMKB_valid : twinsMKB.mValid = true := by decide

theorem twinsMKB_not_extensional : twinsMKB.extensionalB = false := by decide

/-- The two wholes really do have the same proper parts, yet they are different items. -/
theorem twinsMKB_same_parts :
    twinsMKB.properPartsOfL (Qid.wd "w1") = twinsMKB.properPartsOfL (Qid.wd "w2") ∧
    twinsMKB.properPartsOfL (Qid.wd "w1") = [Qid.wd "p1"] := by decide

end Wikidata
