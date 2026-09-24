import Integration.LeastSufficient

/-!
# Observer plurality: turning the corpus's `Bool` ledger into refinement theorems

`Agda/DASHI/Biology/ParentAllyshipMultiObserverBridge.agda` declares six
observer fibres

```agda
data ObserverFibre : Set where
  studentObserver parentAllyObserver teacherObserver
  researcherObserver institutionObserver modelObserver : ObserverFibre
```

and then records its substantive claims as `Bool` fields pinned to `true`:
`childVoiceRemainsDistinct`, `noObserverProjectionEqualsWhole`,
`projectionCannotEraseOtherObservers`,
`studentAndParentObserverFibresRemainDistinct` (re-exported through
`DASHI/Biology/AliceBrownCorpusLoom.agda` and
`DASHI/Governance/AliceBrownInstitutionalAgencyChoiceBridgeExact.agda`).

A `Bool` field with a proof that it equals `true` constrains nothing: it is an
**open socket**, because the record can be inhabited with any projections at
all.  This file supplies what such a field would have to mean, as statements in
the vocabulary of the existing owner `Integration.LeastSufficient`
(`Refines o o'` = everything `o'` reports is computable from what `o` reports),
and proves them on an explicit finite model.

## The owner-level lemma

* `not_refines_of_collapse` — if `o` cannot tell `x` from `y` but `o'` can, then
  `o` does not refine `o'`.  Domain-neutral; every incomparability below is an
  instance.

## The finite model

A situation is a triple of independent binary aspects — read only as three
independent coordinates — and each observer fibre is given a projection:
`student` sees the first, `parentAlly` the second, `institution` the third,
`researcher` the first two, `teacher` the last two, and `model` reports the
parity of all three.

## What is proved on it

* `no_projection_faithful` — **no observer projection equals the whole**: every
  one of the six projections identifies two distinct situations.
* `student_parent_incomparable` — **child voice remains distinct**: neither the
  student nor the parent-ally projection refines the other.
* `pairwise_incomparable_core` — the same for the three single-aspect fibres,
  pairwise.
* `researcher_refines_student`, `researcher_refines_parent`,
  `teacher_refines_institution` — the framework is not vacuous: genuine
  refinements do hold where a fibre sees a superset of coordinates.
* `plurality_jointly_faithful` — **plurality is not incompleteness**: the three
  single-aspect projections *jointly* determine the situation, even though no
  one of them does.  This is the positive statement the `Bool` field cannot
  make.
* `model_incomparable_with_each` — the machine-classification proxy is not a
  substitute for, and is not substituted by, any single situated fibre.

## Claim boundary

The carrier is `Bool × Bool × Bool` and the observers are coordinate
projections.  Nothing here is a claim about students, parents, teachers,
institutions, disability, education practice, or any empirical finding; the
constructor names are labels, and the finite model is a model of the *record
shape*, not of the cited literature.  In particular this file does not show that
the corpus's own six projections have these properties — it shows what would
have to be exhibited for the `Bool` fields to carry content.
-/

namespace Integration.ObserverPlurality

open Integration.LeastSufficient

/-! ## The owner-level lemma -/

/-- **Collapse refutes refinement.**  If `o` identifies `x` and `y` while `o'`
separates them, `o` does not refine `o'`. -/
theorem not_refines_of_collapse {X Y Z : Type} {o : X → Y} {o' : X → Z} {x y : X}
    (h : o x = o y) (h' : o' x ≠ o' y) : ¬ Refines o o' := by
  rintro ⟨f, hf⟩
  exact h' (by rw [hf x, hf y, h])

/-- A family of observers is **jointly faithful** when together they separate
points. -/
def JointlyFaithful {X Y : Type} {ι : Type} (o : ι → X → Y) : Prop :=
  ∀ x y : X, (∀ i, o i x = o i y) → x = y

/-! ## The finite model -/

/-- Mirror of `ParentAllyshipMultiObserverBridge.ObserverFibre`. -/
inductive ObserverFibre
  | studentObserver | parentAllyObserver | teacherObserver
  | researcherObserver | institutionObserver | modelObserver
  deriving DecidableEq, Repr, Fintype

/-- The canonical enumeration, in the Agda module's order. -/
def canonicalObserverFibres : List ObserverFibre :=
  [.studentObserver, .parentAllyObserver, .teacherObserver,
   .researcherObserver, .institutionObserver, .modelObserver]

theorem canonicalObserverFibres_nodup : canonicalObserverFibres.Nodup := by decide

theorem canonicalObserverFibres_complete (o : ObserverFibre) :
    o ∈ canonicalObserverFibres := by decide +revert

/-- A situation: three independent binary coordinates. -/
abbrev Situation := Bool × Bool × Bool

/-- Single-coordinate projections. -/
def student (s : Situation) : Bool := s.1

/-- The parent-ally fibre sees the second coordinate. -/
def parentAlly (s : Situation) : Bool := s.2.1

/-- The institution fibre sees the third coordinate. -/
def institution (s : Situation) : Bool := s.2.2

/-- The researcher fibre sees the first two coordinates. -/
def researcher (s : Situation) : Bool × Bool := (s.1, s.2.1)

/-- The teacher fibre sees the last two coordinates. -/
def teacher (s : Situation) : Bool × Bool := (s.2.1, s.2.2)

/-- The model fibre reports the parity of all three coordinates. -/
def model (s : Situation) : Bool := xor s.1 (xor s.2.1 s.2.2)

/-! ## No projection equals the whole -/

theorem student_not_injective : ¬ Function.Injective student := by
  intro h
  exact absurd (h (a₁ := (true, true, true)) (a₂ := (true, false, false)) rfl) (by decide)

theorem parentAlly_not_injective : ¬ Function.Injective parentAlly := by
  intro h
  exact absurd (h (a₁ := (true, true, true)) (a₂ := (false, true, false)) rfl) (by decide)

theorem institution_not_injective : ¬ Function.Injective institution := by
  intro h
  exact absurd (h (a₁ := (true, true, true)) (a₂ := (false, false, true)) rfl) (by decide)

theorem researcher_not_injective : ¬ Function.Injective researcher := by
  intro h
  exact absurd (h (a₁ := (true, true, true)) (a₂ := (true, true, false)) rfl) (by decide)

theorem teacher_not_injective : ¬ Function.Injective teacher := by
  intro h
  exact absurd (h (a₁ := (true, true, true)) (a₂ := (false, true, true)) rfl) (by decide)

theorem model_not_injective : ¬ Function.Injective model := by
  intro h
  exact absurd (h (a₁ := (true, true, false)) (a₂ := (false, false, false)) rfl) (by decide)

/-- **No observer projection equals the whole.** -/
theorem no_projection_faithful :
    ¬ Function.Injective student ∧ ¬ Function.Injective parentAlly ∧
    ¬ Function.Injective institution ∧ ¬ Function.Injective researcher ∧
    ¬ Function.Injective teacher ∧ ¬ Function.Injective model :=
  ⟨student_not_injective, parentAlly_not_injective, institution_not_injective,
   researcher_not_injective, teacher_not_injective, model_not_injective⟩

/-! ## Incomparability -/

/-- **Child voice remains distinct**: neither of the two fibres refines the
other. -/
theorem student_parent_incomparable :
    ¬ Refines student parentAlly ∧ ¬ Refines parentAlly student :=
  ⟨not_refines_of_collapse (x := (true, true, true)) (y := (true, false, true)) rfl (by decide),
   not_refines_of_collapse (x := (true, true, true)) (y := (false, true, true)) rfl (by decide)⟩

/-- The three single-aspect fibres are pairwise incomparable. -/
theorem pairwise_incomparable_core :
    ¬ Refines student institution ∧ ¬ Refines institution student ∧
    ¬ Refines parentAlly institution ∧ ¬ Refines institution parentAlly :=
  ⟨not_refines_of_collapse (x := (true, true, true)) (y := (true, true, false)) rfl (by decide),
   not_refines_of_collapse (x := (true, true, true)) (y := (false, true, true)) rfl (by decide),
   not_refines_of_collapse (x := (true, true, true)) (y := (true, true, false)) rfl (by decide),
   not_refines_of_collapse (x := (true, true, true)) (y := (true, false, true)) rfl (by decide)⟩

/-- The machine proxy neither refines nor is refined by any single situated
fibre. -/
theorem model_incomparable_with_each :
    ¬ Refines model student ∧ ¬ Refines student model ∧
    ¬ Refines model parentAlly ∧ ¬ Refines parentAlly model ∧
    ¬ Refines model institution ∧ ¬ Refines institution model :=
  ⟨not_refines_of_collapse (x := (true, true, false)) (y := (false, false, false)) rfl (by decide),
   not_refines_of_collapse (x := (true, true, true)) (y := (true, true, false)) rfl (by decide),
   not_refines_of_collapse (x := (true, true, false)) (y := (false, false, false)) rfl (by decide),
   not_refines_of_collapse (x := (true, true, true)) (y := (false, true, true)) rfl (by decide),
   not_refines_of_collapse (x := (true, true, false)) (y := (true, false, true)) rfl (by decide),
   not_refines_of_collapse (x := (true, true, true)) (y := (true, false, true)) rfl (by decide)⟩

/-! ## Genuine refinements -/

theorem researcher_refines_student : Refines researcher student :=
  ⟨fun p => p.1, fun _ => rfl⟩

theorem researcher_refines_parent : Refines researcher parentAlly :=
  ⟨fun p => p.2, fun _ => rfl⟩

theorem teacher_refines_institution : Refines teacher institution :=
  ⟨fun p => p.2, fun _ => rfl⟩

theorem teacher_refines_parent : Refines teacher parentAlly :=
  ⟨fun p => p.1, fun _ => rfl⟩

/-! ## Plurality is not incompleteness -/

/-- The three single-aspect fibres, as one family. -/
def coreFamily : Fin 3 → Situation → Bool
  | 0 => student
  | 1 => parentAlly
  | 2 => institution

/-- **Jointly faithful.**  No single fibre determines the situation, yet the
three together do. -/
theorem plurality_jointly_faithful : JointlyFaithful coreFamily := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  simp [coreFamily, student, parentAlly, institution] at h0 h1 h2
  simp [h0, h1, h2]

/-- The parity proxy adds nothing once the three aspects are known: it is
refined by the whole family, and indeed by the researcher/institution pair. -/
theorem model_refined_by_researcher_and_institution :
    Refines (fun s => (researcher s, institution s)) model :=
  ⟨fun p => xor p.1.1 (xor p.1.2 p.2), fun _ => rfl⟩

/-! ## The corpus's own projection record is a label, not an observer -/

/-- Mirror of `ParentAllyshipMultiObserverBridge.ObserverProjection`: an observer
fibre, a label, and three `Bool` fields each pinned to `true`. -/
structure ObserverProjection where
  /-- Which fibre. -/
  observer : ObserverFibre
  /-- A prose label. -/
  projectionLabel : String
  /-- "The projection is situated". -/
  projectionIsSituated : Bool
  /-- Pinned true. -/
  projectionIsSituatedIsTrue : projectionIsSituated = true
  /-- "The projection is not the whole system". -/
  projectionNotWholeSystem : Bool
  /-- Pinned true. -/
  projectionNotWholeSystemIsTrue : projectionNotWholeSystem = true
  /-- "The projection cannot erase other observers". -/
  projectionCannotEraseOtherObservers : Bool
  /-- Pinned true. -/
  projectionCannotEraseOtherObserversIsTrue : projectionCannotEraseOtherObservers = true

/-- **The record contains no projection.**  It is equivalent to a fibre tag and
a string: the three pinned flags add nothing, and no field mentions a map out of
any carrier.  So the Agda `ObserverProjection` cannot state, let alone prove,
any of the incomparability facts above; that is the precise sense in which it is
an open socket. -/
def projectionRecordIsLabel : ObserverProjection ≃ (ObserverFibre × String) where
  toFun p := (p.observer, p.projectionLabel)
  invFun q := ⟨q.1, q.2, true, rfl, true, rfl, true, rfl⟩
  left_inv := by rintro ⟨o, l, _, rfl, _, rfl, _, rfl⟩; rfl
  right_inv _ := rfl

end Integration.ObserverPlurality
