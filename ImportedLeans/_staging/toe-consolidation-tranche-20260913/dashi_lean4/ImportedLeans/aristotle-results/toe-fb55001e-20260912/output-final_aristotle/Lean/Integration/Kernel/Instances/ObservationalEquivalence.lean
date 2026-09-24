import Integration.Kernel.Probe
import Integration.Experiment.ObservationalEquivalence

/-!
# The observational-equivalence lane is a thin instance of the kernel

`Integration.Experiment.ObservationalEquivalence` compares *theories* through
the distinctions an experiment language `L` forces, and proves antitonicity of
the equivalence classes directly.  This file shows that this lane, too, is the
residual-fibre calculus of `Integration.Kernel.ResidualFibre`, with the
hypothesis fibre living in the space of theories rather than in a parameter
space.

The dictionary:

* the residual fibre is a set of *candidate theories*;
* an experiment `e` is a kernel channel `predChannel e`, reading off the set of
  outcomes a theory permits for `e`;
* running `e` and finding that the world agrees with the reference theory `H`
  is the kernel event `agreesEvent e H`;
* **`obsClass_eq_refineAll`** — the observational equivalence class of `H`
  relative to a finite language `L` *is* the kernel's iterated backward
  refinement of the full space of theories by those events.

From that identification the lane's structural theorems are kernel instances:

* `obsClass_append_eq_refineAll` — enlarging the language is further
  refinement, so `obsClass_antitone` is `refineAll_refines`;
* `separates_iff_discriminates` — a separating experiment is exactly a
  discriminating kernel probe on the pair;
* `strictly_refines_iff_separates` — an experiment strictly shrinks the class
  iff it separates some member of it, the lane form of
  `strictly_refines_iff_discriminates`;
* `redundant_experiment_does_not_refine` — an experiment on which the whole
  surviving fibre already agrees contributes nothing.

And the lane inherits the kernel's refusal:
`class_narrowing_is_not_theory_identification` instantiates
`narrower_not_mechanism` — a strictly smaller equivalence class still need not
settle a consumer question about the theory.
-/

namespace Integration.Kernel.Instances.ObservationalEquivalenceBridge

open Set Integration.Kernel.ResidualFibre Integration.Kernel.Probe
open Integration.Experiment.ObservationalEquivalence

variable {E O : Type*}

/-! ## §1 An experiment as a kernel channel -/

/-- The channel that reads off what a candidate theory permits for `e`. -/
def predChannel (e : E) : Channel (Theory E O) (Set O) := ⟨fun H => H.Pred e⟩

/-- Running `e` and finding agreement with the reference theory `H`. -/
def agreesEvent (e : E) (H : Theory E O) : Set (Theory E O) :=
  event (predChannel e) (H.Pred e)

@[simp] theorem mem_agreesEvent {e : E} {H H' : Theory E O} :
    H' ∈ agreesEvent e H ↔ H'.Pred e = H.Pred e := Iff.rfl

/-! ## §2 The identification -/

theorem refineAll_agreesEvents (P : Set (Theory E O)) (L : List E) (H : Theory E O) :
    refineAll P (L.map (fun e => agreesEvent e H)) =
      {H' | H' ∈ P ∧ ∀ e ∈ L, H'.Pred e = H.Pred e} := by
  induction L generalizing P with
  | nil => ext H'; simp
  | cons e L ih =>
      ext H'
      simp only [List.map_cons, refineAll_cons, ih, mem_setOf_eq, refineBy, mem_inter_iff,
        mem_agreesEvent, List.mem_cons]
      constructor
      · rintro ⟨⟨hP, he⟩, hL⟩
        exact ⟨hP, by rintro e' (rfl | he') ; exacts [he, hL e' he']⟩
      · rintro ⟨hP, hall⟩
        exact ⟨⟨hP, hall e (Or.inl rfl)⟩, fun e' he' => hall e' (Or.inr he')⟩

/-- **The observational equivalence class is the kernel's iterated refinement.**
The class of `H` relative to the language `L` is what is left of the space of
all theories after each experiment in `L` has been run and found to agree with
`H`. -/
theorem obsClass_eq_refineAll (L : List E) (H : Theory E O) :
    obsClass {e | e ∈ L} H = refineAll univ (L.map (fun e => agreesEvent e H)) := by
  rw [refineAll_agreesEvents]
  ext H'
  simp only [mem_obsClass, ObsEquiv, mem_setOf_eq, mem_univ, true_and]
  exact ⟨fun h e he => (h e he).symm, fun h e he => (h e he).symm⟩

/-- Enlarging the language is further kernel refinement of the class already
obtained. -/
theorem obsClass_append_eq_refineAll (L L' : List E) (H : Theory E O) :
    obsClass {e | e ∈ L ++ L'} H =
      refineAll (obsClass {e | e ∈ L} H) (L'.map (fun e => agreesEvent e H)) := by
  rw [obsClass_eq_refineAll, obsClass_eq_refineAll, List.map_append, refineAll_append]

/-- `obsClass_antitone` for the list form, re-derived as `refineAll_refines`. -/
theorem obsClass_append_refines (L L' : List E) (H : Theory E O) :
    Refines (obsClass {e | e ∈ L ++ L'} H) (obsClass {e | e ∈ L} H) := by
  rw [obsClass_append_eq_refineAll]
  exact refineAll_refines _ _

/-! ## §3 A separating experiment is a discriminating probe -/

/-- **Separation is kernel discrimination.**  An experiment separates two
theories exactly when, viewed as a channel, it collides on the pair. -/
theorem separates_iff_discriminates (e : E) (H₁ H₂ : Theory E O) :
    Separates e H₁ H₂ ↔ Discriminates (predChannel e) ({H₁, H₂} : Set (Theory E O)) := by
  constructor
  · intro h
    exact ⟨H₁, by simp, H₂, by simp, h⟩
  · rintro ⟨w₁, hw₁, w₂, hw₂, hne⟩
    rcases hw₁ with rfl | rfl <;> rcases hw₂ with rfl | rfl
    · exact absurd rfl hne
    · exact hne
    · exact fun h => hne h.symm
    · exact absurd rfl hne

/-- **An experiment strictly shrinks the class iff it separates a member of it.**
The lane form of `strictly_refines_iff_discriminates`, specialised to the
reference theory's own reading. -/
theorem strictly_refines_iff_separates (e : E) (H : Theory E O) (F : Set (Theory E O)) :
    refineBy F (agreesEvent e H) ⊂ F ↔ ∃ H' ∈ F, Separates e H H' := by
  constructor
  · rintro ⟨-, hns⟩
    by_contra hcon
    simp only [Separates, not_exists, not_and, not_not] at hcon
    exact hns fun H' hH' => ⟨hH', (hcon H' hH').symm⟩
  · rintro ⟨H', hH', hsep⟩
    exact ⟨inter_subset_left, fun hsub => hsep ((hsub hH').2).symm⟩

/-- A **redundant** experiment refines nothing: if every candidate in the fibre
already agrees with the reference theory at `e`, admitting `e` leaves the fibre
unchanged.  This is `refine_eq_self_of_constant` in the theory lane. -/
theorem redundant_experiment_does_not_refine (e : E) (H : Theory E O) (F : Set (Theory E O))
    (hconst : ∀ H' ∈ F, H'.Pred e = H.Pred e) :
    refineBy F (agreesEvent e H) = F :=
  inter_eq_self_of_subset_left fun H' hH' => hconst H' hH'

/-! ## §4 The lane inherits the kernel's refusal -/

/-- Reference theory: permits every outcome of experiment `false`, none of
experiment `true`. -/
def refTheory : Theory Bool Bool := ⟨fun b => if b then ∅ else univ⟩

/-- A theory permitting every outcome of every experiment. -/
def allTheory : Theory Bool Bool := ⟨fun _ => univ⟩

/-- A theory permitting no outcome of any experiment. -/
def noneTheory : Theory Bool Bool := ⟨fun _ => ∅⟩

/-- The consumer question: does the theory forbid every outcome of experiment
`true`? -/
def forbidsTrue (H : Theory Bool Bool) : Prop := H.Pred true = ∅

theorem univ_bool_ne_empty : (univ : Set Bool) ≠ ∅ := by
  intro h
  have : (true : Bool) ∈ (∅ : Set Bool) := h ▸ mem_univ true
  exact this

theorem mem_class_of_agrees {H' : Theory Bool Bool} (h : H'.Pred false = univ) :
    H' ∈ obsClass {e | e ∈ [false]} refTheory := by
  intro e he
  have : e = false := by simpa using he
  subst this
  simp [refTheory, h]

/-- **A strictly smaller equivalence class need not identify the theory.**
The language `[false]` cuts the space of theories down strictly — it rules out
`noneTheory` — yet the consumer question `forbidsTrue`, about what the theory
says of the *unavailable* experiment, remains open inside the surviving class.
This is `narrower_not_mechanism` in the theory-comparison lane. -/
theorem class_narrowing_is_not_theory_identification :
    obsClass {e | e ∈ [false]} refTheory ⊂ univ ∧
      (obsClass {e | e ∈ [false]} refTheory).Nonempty ∧
      ¬ Determines (obsClass {e | e ∈ [false]} refTheory) forbidsTrue := by
  refine ⟨⟨subset_univ _, fun hsub => ?_⟩,
    ⟨allTheory, mem_class_of_agrees rfl⟩, ?_⟩
  · have h := hsub (mem_univ noneTheory) false (by simp)
    simp only [refTheory, noneTheory, if_neg (Bool.false_ne_true)] at h
    exact univ_bool_ne_empty h
  · rintro ⟨v, hv⟩
    have h1 := hv refTheory (mem_class_of_agrees (by simp [refTheory]))
    have h2 := hv allTheory (mem_class_of_agrees rfl)
    rw [← h2] at h1
    simp only [forbidsTrue, refTheory, allTheory, if_true, eq_iff_iff, true_iff] at h1
    exact univ_bool_ne_empty h1

end Integration.Kernel.Instances.ObservationalEquivalenceBridge
