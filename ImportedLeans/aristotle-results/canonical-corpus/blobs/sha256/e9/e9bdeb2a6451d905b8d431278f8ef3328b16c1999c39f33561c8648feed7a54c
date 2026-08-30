import RequestProject.Ranks

/-!
# Snak types: `some value` and `no value`

A Wikidata statement does not have to carry a value.  Its *snak* is one of three
things:

* an ordinary **value**,
* **`somevalue`** — the property does have a value for this item, but it is
  unknown ("the father of this person is someone, we do not know who"), or
* **`novalue`** — the property has **no** value for this item ("this person has
  no children").

The last two are genuinely logical statements: `somevalue` is an existential
claim and `novalue` a negative one, and a knowledge base can therefore be
*inconsistent* in a way that a base of plain values never is.  This file gives
the snak layer a model theory and settles exactly when it is consistent.

An *assignment* records, for each item and property, the set of values the item
really has; it **models** a base when every snak of the base comes out true.
Main results:

* a value entails `somevalue`, and a base containing `novalue` together with a
  value (or a `somevalue`) for the same item and property has **no model**;
* **the consistency criterion** (`Wikidata.SnakBase.satisfiable_iff_clashFree`):
  a base has a model exactly when it has no such clash — and the clash test is
  executable, so consistency of the snak layer is decidable;
* what a consistent base **entails**: it entails `novalue` for an item and
  property exactly when it asserts it, and it entails `somevalue` exactly when
  it asserts a value or a `somevalue`
  (`Wikidata.SnakBase.entails_noValue_iff`, `...entails_someValue_iff`).  So the
  snak layer says neither more nor less than what is written in it.
-/

namespace Wikidata

/-- The snak of a statement: a value, an unknown value (`somevalue`), or no value
at all (`novalue`). -/
inductive Snak where
  /-- An ordinary value. -/
  | value (v : Value)
  /-- `somevalue`: there is a value, but it is unknown. -/
  | someValue
  /-- `novalue`: the property has no value for this subject. -/
  | noValue
deriving DecidableEq, Repr, Inhabited

/-- A statement of the snak layer: a subject, a property and a snak. -/
structure SnakStmt where
  /-- The subject item. -/
  subj : Qid
  /-- The property. -/
  prop : Qid
  /-- The snak. -/
  snak : Snak
deriving DecidableEq, Repr, Inhabited

/-- A knowledge base of the snak layer. -/
abbrev SnakBase := List SnakStmt

/-- An assignment: the values each item really has for each property. -/
def Assignment := Qid → Qid → Set Value

namespace SnakBase

/-- When an assignment makes a statement true. -/
def Satisfies (A : Assignment) (st : SnakStmt) : Prop :=
  match st.snak with
  | .value v => v ∈ A st.subj st.prop
  | .someValue => (A st.subj st.prop).Nonempty
  | .noValue => A st.subj st.prop = ∅

/-- An assignment models a base when it makes every statement true. -/
def Models (A : Assignment) (B : SnakBase) : Prop := ∀ st ∈ B, Satisfies A st

/-- A base is satisfiable when it has a model. -/
def Satisfiable (B : SnakBase) : Prop := ∃ A, Models A B

/-- What a base entails: what holds in each of its models. -/
def Entails (B : SnakBase) (st : SnakStmt) : Prop := ∀ A, Models A B → Satisfies A st

/-- A value entails `somevalue`. -/
theorem satisfies_someValue_of_value {A : Assignment} {s p : Qid} {v : Value}
    (h : Satisfies A ⟨s, p, .value v⟩) : Satisfies A ⟨s, p, .someValue⟩ := ⟨v, h⟩

/-- **A `novalue` snak clashes with a value snak**: no assignment satisfies both. -/
theorem not_satisfiable_of_value_and_noValue {B : SnakBase} {s p : Qid} {v : Value}
    (h₁ : (⟨s, p, .value v⟩ : SnakStmt) ∈ B) (h₂ : (⟨s, p, .noValue⟩ : SnakStmt) ∈ B) :
    ¬ Satisfiable B := by
  rintro ⟨A, hA⟩
  have hv : v ∈ A s p := hA _ h₁
  have he : A s p = ∅ := hA _ h₂
  rw [he] at hv
  exact hv

/-- **A `novalue` snak clashes with a `somevalue` snak.** -/
theorem not_satisfiable_of_someValue_and_noValue {B : SnakBase} {s p : Qid}
    (h₁ : (⟨s, p, .someValue⟩ : SnakStmt) ∈ B) (h₂ : (⟨s, p, .noValue⟩ : SnakStmt) ∈ B) :
    ¬ Satisfiable B := by
  rintro ⟨A, hA⟩
  obtain ⟨v, hv⟩ : (A s p).Nonempty := hA _ h₁
  have he : A s p = ∅ := hA _ h₂
  rw [he] at hv
  exact hv

/-! ### The consistency criterion -/

/-- A base is *clash-free* when a `novalue` snak is never accompanied by another
snak for the same subject and property. -/
def ClashFree (B : SnakBase) : Prop :=
  ∀ s p, (⟨s, p, .noValue⟩ : SnakStmt) ∈ B → ∀ st ∈ B, st.subj = s → st.prop = p →
    st.snak = .noValue

/-- The executable clash test. -/
def clashFreeB (B : SnakBase) : Bool :=
  B.all (fun st =>
    match st.snak with
    | .noValue =>
        B.all (fun st' =>
          !(st'.subj == st.subj && st'.prop == st.prop) || (st'.snak == Snak.noValue))
    | _ => true)

theorem clashFreeB_iff {B : SnakBase} : clashFreeB B = true ↔ ClashFree B := by
  simp only [clashFreeB, ClashFree, List.all_eq_true]
  constructor
  · intro h s p hmem st hst hs hp
    have := h _ hmem
    simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, beq_iff_eq,
      beq_eq_false_iff_ne, ne_eq, List.all_eq_true] at this
    rcases this st hst with h₁ | h₁
    · rcases h₁ with h₁ | h₁
      · exact absurd hs h₁
      · exact absurd hp h₁
    · simpa using h₁
  · intro h st hst
    cases hsn : st.snak with
    | value v => simp
    | someValue => simp
    | noValue =>
        simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
          Bool.and_eq_false_iff, beq_iff_eq, beq_eq_false_iff_ne, ne_eq]
        intro st' hst'
        by_cases hs : st'.subj = st.subj
        · by_cases hp : st'.prop = st.prop
          · refine Or.inr ?_
            have hmem : (⟨st.subj, st.prop, .noValue⟩ : SnakStmt) ∈ B := by
              obtain ⟨a, b, c⟩ := st; simp_all
            simpa using h _ _ hmem st' hst' hs hp
          · exact Or.inl (Or.inr hp)
        · exact Or.inl (Or.inl hs)

/-- The canonical assignment of a base: the asserted values, plus one anonymous
value wherever a `somevalue` snak asks for one. -/
def canonical (B : SnakBase) : Assignment := fun s p =>
  {v | (⟨s, p, .value v⟩ : SnakStmt) ∈ B} ∪
    {v | (⟨s, p, .someValue⟩ : SnakStmt) ∈ B ∧ v = Value.str "some value"}

theorem models_canonical {B : SnakBase} (h : ClashFree B) : Models (canonical B) B := by
  rintro ⟨s, p, sn⟩ hst
  cases sn with
  | value v =>
      show v ∈ canonical B s p
      exact Or.inl hst
  | someValue =>
      show (canonical B s p).Nonempty
      exact ⟨Value.str "some value", Or.inr ⟨hst, rfl⟩⟩
  | noValue =>
      show canonical B s p = ∅
      refine Set.eq_empty_iff_forall_notMem.2 ?_
      rintro v (hv | ⟨hv, -⟩)
      · have := h _ _ hst _ hv rfl rfl
        simp at this
      · have := h _ _ hst _ hv rfl rfl
        simp at this

/-- **The consistency criterion**: a snak base has a model exactly when it is
clash-free, so the consistency of the snak layer is decided by `clashFreeB`. -/
theorem satisfiable_iff_clashFree {B : SnakBase} : Satisfiable B ↔ ClashFree B := by
  constructor
  · intro hsat s p hmem st hst hs hp
    cases hsn : st.snak with
    | value v =>
        exfalso
        refine not_satisfiable_of_value_and_noValue (s := s) (p := p) (v := v) ?_ hmem hsat
        obtain ⟨a, b, c⟩ := st; simp_all
    | someValue =>
        exfalso
        refine not_satisfiable_of_someValue_and_noValue (s := s) (p := p) ?_ hmem hsat
        obtain ⟨a, b, c⟩ := st; simp_all
    | noValue => rfl
  · intro h
    exact ⟨canonical B, models_canonical h⟩

theorem satisfiable_iff_clashFreeB {B : SnakBase} : Satisfiable B ↔ clashFreeB B = true := by
  rw [satisfiable_iff_clashFree, clashFreeB_iff]

/-! ### What a base entails -/

/-- Everything asserted is entailed. -/
theorem entails_of_mem {B : SnakBase} {st : SnakStmt} (h : st ∈ B) : Entails B st :=
  fun _ hA => hA _ h

/-- Entailment is monotone: a larger base entails more. -/
theorem entails_mono {B B' : SnakBase} (h : ∀ st ∈ B, st ∈ B') {st : SnakStmt}
    (hst : Entails B st) : Entails B' st :=
  fun A hA => hst A fun st' hst' => hA st' (h st' hst')

/-- An asserted value entails `somevalue`. -/
theorem entails_someValue_of_value {B : SnakBase} {s p : Qid} {v : Value}
    (h : (⟨s, p, .value v⟩ : SnakStmt) ∈ B) : Entails B ⟨s, p, .someValue⟩ :=
  fun _ hA => satisfies_someValue_of_value (hA _ h)

/-- The canonical assignment with one extra value at a chosen subject–property
pair; used to show that nothing unasserted is entailed. -/
def canonicalPlus (B : SnakBase) (s p : Qid) : Assignment := fun s' p' =>
  if s' = s ∧ p' = p then insert (Value.str "some value") (canonical B s' p')
  else canonical B s' p'

theorem models_canonicalPlus {B : SnakBase} (h : ClashFree B) {s p : Qid}
    (hno : (⟨s, p, .noValue⟩ : SnakStmt) ∉ B) : Models (canonicalPlus B s p) B := by
  rintro ⟨s', p', sn⟩ hst
  have hcan := models_canonical h _ hst
  cases sn with
  | value v =>
      have hv : v ∈ canonical B s' p' := hcan
      show v ∈ canonicalPlus B s p s' p'
      unfold canonicalPlus
      split
      · exact Set.mem_insert_of_mem _ hv
      · exact hv
  | someValue =>
      have hv : (canonical B s' p').Nonempty := hcan
      show (canonicalPlus B s p s' p').Nonempty
      unfold canonicalPlus
      split
      · obtain ⟨v, hv⟩ := hv
        exact ⟨v, Set.mem_insert_of_mem _ hv⟩
      · exact hv
  | noValue =>
      have hv : canonical B s' p' = ∅ := hcan
      have hne : ¬ (s' = s ∧ p' = p) := by
        rintro ⟨rfl, rfl⟩
        exact hno hst
      show canonicalPlus B s p s' p' = ∅
      unfold canonicalPlus
      rw [if_neg hne]
      exact hv

/-- **A consistent base entails `novalue` exactly when it asserts it.** -/
theorem entails_noValue_iff {B : SnakBase} (hsat : Satisfiable B) {s p : Qid} :
    Entails B ⟨s, p, .noValue⟩ ↔ (⟨s, p, .noValue⟩ : SnakStmt) ∈ B := by
  constructor
  · intro h
    by_contra hno
    have hcf : ClashFree B := satisfiable_iff_clashFree.1 hsat
    have hmod := models_canonicalPlus hcf hno
    have : canonicalPlus B s p s p = ∅ := h _ hmod
    have hmem : Value.str "some value" ∈ canonicalPlus B s p s p := by
      unfold canonicalPlus
      rw [if_pos ⟨rfl, rfl⟩]
      exact Set.mem_insert _ _
    rw [this] at hmem
    exact hmem
  · exact entails_of_mem

/-- **A consistent base entails `somevalue` exactly when it asserts a value or a
`somevalue`.** -/
theorem entails_someValue_iff {B : SnakBase} (hsat : Satisfiable B) {s p : Qid} :
    Entails B ⟨s, p, .someValue⟩ ↔
      (⟨s, p, .someValue⟩ : SnakStmt) ∈ B ∨ ∃ v, (⟨s, p, .value v⟩ : SnakStmt) ∈ B := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    obtain ⟨hsome, hval⟩ := hcon
    have hcf : ClashFree B := satisfiable_iff_clashFree.1 hsat
    obtain ⟨v, hv⟩ : (canonical B s p).Nonempty := h _ (models_canonical hcf)
    rcases hv with hv | ⟨hv, -⟩
    · exact hval v hv
    · exact hsome hv
  · rintro (h | ⟨v, h⟩)
    · exact entails_of_mem h
    · exact entails_someValue_of_value h

/-! ### Reading off the values -/

/-- The values a base records for a subject and property; `somevalue` and
`novalue` snaks contribute nothing. -/
def valuesOf (B : SnakBase) (s p : Qid) : List Value :=
  B.filterMap (fun st =>
    if st.subj = s ∧ st.prop = p then
      match st.snak with
      | .value v => some v
      | _ => none
    else none)

theorem mem_valuesOf_iff {B : SnakBase} {s p : Qid} {v : Value} :
    v ∈ valuesOf B s p ↔ (⟨s, p, .value v⟩ : SnakStmt) ∈ B := by
  simp only [valuesOf, List.mem_filterMap]
  constructor
  · rintro ⟨st, hst, hsome⟩
    by_cases hc : st.subj = s ∧ st.prop = p
    · rw [if_pos hc] at hsome
      obtain ⟨a, b, c⟩ := st
      cases c with
      | value w => simp_all
      | someValue => simp at hsome
      | noValue => simp at hsome
    · rw [if_neg hc] at hsome
      simp at hsome
  · intro h
    exact ⟨⟨s, p, .value v⟩, h, by simp⟩

/-- An item with a `novalue` snak has no recorded values, in a clash-free base. -/
theorem valuesOf_eq_nil_of_noValue {B : SnakBase} (h : ClashFree B) {s p : Qid}
    (hno : (⟨s, p, .noValue⟩ : SnakStmt) ∈ B) : valuesOf B s p = [] := by
  refine List.eq_nil_iff_forall_not_mem.2 ?_
  intro v hv
  have := h _ _ hno _ (mem_valuesOf_iff.1 hv) rfl rfl
  simp at this

end SnakBase

/-! ## A worked fragment -/

namespace SnakExample

open Wikidata Wikidata.SnakBase

/-- Elizabeth I of England (Q7207). -/
def elizabeth : Qid := .wd "Q7207"
/-- Douglas Adams (Q42). -/
def adams : Qid := .wd "Q42"
/-- `child` (P40). -/
def child : Qid := .wd "P40"
/-- `father` (P22). -/
def father : Qid := .wd "P22"
/-- `spouse` (P26). -/
def spouse : Qid := .wd "P26"
/-- Jane Belson (Q15873243), Douglas Adams' wife. -/
def jane : Qid := .wd "Q15873243"

/-- Elizabeth I had no children (`novalue`); Douglas Adams' spouse is recorded
with a value, and the father of an unnamed person is recorded as `somevalue`. -/
def frag : SnakBase :=
  [⟨elizabeth, child, .noValue⟩,
   ⟨adams, spouse, .value (.item jane)⟩,
   ⟨adams, father, .someValue⟩]

theorem frag_clashFree : clashFreeB frag = true := by decide

theorem frag_satisfiable : Satisfiable frag :=
  satisfiable_iff_clashFreeB.2 frag_clashFree

/-- The base entails that Adams has some father — that is what the `somevalue`
snak says — ... -/
theorem frag_entails_father : Entails frag ⟨adams, father, .someValue⟩ :=
  entails_of_mem (by decide)

/-- ... and it entails that he has some spouse, which it does *not* say
explicitly: the value entails the existential. -/
theorem frag_entails_spouse : Entails frag ⟨adams, spouse, .someValue⟩ :=
  entails_someValue_of_value (v := .item jane) (by decide)

/-- It does not entail that Adams has a child: nothing is recorded either way. -/
theorem frag_not_entails_child : ¬ Entails frag ⟨adams, child, .noValue⟩ := by
  rw [entails_noValue_iff frag_satisfiable]
  decide

/-- Elizabeth's `novalue` snak is entailed, and no value is recorded for it. -/
theorem frag_entails_no_child : Entails frag ⟨elizabeth, child, .noValue⟩ :=
  entails_of_mem (by decide)

theorem frag_no_children : valuesOf frag elizabeth child = [] := by decide

/-- Adding a child of Elizabeth I to the base makes it inconsistent. -/
def fragBad : SnakBase := ⟨elizabeth, child, .value (.item (.wd "Q1"))⟩ :: frag

theorem fragBad_not_clashFree : clashFreeB fragBad = false := by decide

theorem fragBad_unsatisfiable : ¬ Satisfiable fragBad := by
  intro h
  have := satisfiable_iff_clashFreeB.1 h
  rw [fragBad_not_clashFree] at this
  exact Bool.noConfusion this

/-- Recording `somevalue` for a property that is also declared to have no value is
just as inconsistent. -/
def fragBad2 : SnakBase := ⟨elizabeth, child, .someValue⟩ :: frag

theorem fragBad2_unsatisfiable : ¬ Satisfiable fragBad2 :=
  not_satisfiable_of_someValue_and_noValue (s := elizabeth) (p := child) (by decide) (by decide)

end SnakExample

end Wikidata
