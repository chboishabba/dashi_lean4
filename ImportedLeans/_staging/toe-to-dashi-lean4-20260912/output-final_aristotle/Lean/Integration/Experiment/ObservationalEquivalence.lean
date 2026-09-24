import Mathlib
import Integration.Experiment.RCCircuit

/-!
# Stage 7 / Stage 9 seed — observational equivalence relative to an experiment language

Everything upstream in the Stage 4–7 chain compares *parameters* inside a fixed
family.  This file takes the step up and compares *theories*, and it does so in
the only way the rest of the development licenses: through the observable
distinctions the theories force.

A **theory** here is nothing but an interface: for each experiment it declares
the set of outcomes it permits.

```
H : E → Set O
```

An **experiment language** is a set `L ⊆ E` of experiments that are actually
available.  Two theories are *observationally equivalent relative to `L`* when

```
H₁ ∼_L H₂   ⟺   ∀ e ∈ L, Pred(H₁, e) = Pred(H₂, e).
```

## What is proved

| Statement | Kind | Content |
|---|---|---|
| `ObsEquiv` | definition | `∀ e ∈ L, Pred H₁ e = Pred H₂ e` |
| `obsEquiv_refl/symm/trans`, `obsEquiv_equivalence` | theorem | it is an equivalence relation for each `L` |
| `obsEquiv_empty` | theorem | with no experiments every theory is equivalent to every other |
| `obsEquiv_antitone` | theorem | a *larger* language is a *finer* relation |
| `obsClass_antitone` | theorem | so equivalence classes shrink as the language grows: **new experiments refine the observational equivalence classes of theories** |
| `not_obsEquiv_iff_exists_separating` | theorem | inequivalence is exactly the existence of a separating experiment in `L` |
| `obsEquiv_transfers_refutation` | theorem | an `L`-experiment refuting one of two `L`-equivalent theories refutes the other: within `L` they are the same scientific object |
| **`rc_theories_equivalent_for_voltage_only`** | theorem | in the RC language of voltage samples, `(R,C)` and `(2R, C/2)` are observationally equivalent |
| **`ohmmeter_splits_the_class`** | theorem | adding a single resistance measurement to the language splits that class |
| `equivalent_theories_need_not_be_equal` | theorem (negative) | observational equivalence relative to `L` does not identify theories |
| **`pairwise_separation_does_not_give_one_discriminating_experiment`** | theorem (negative) | three theories, pairwise separated inside `L`, with no single experiment in `L` telling all three apart |

## Claim boundary

`Theory` is a declared outcome-set assignment; nothing here says that any
particular physical theory has this shape, and `Pred` carries no probability.
"Equivalent" always means *equivalent for the stated language*, never
"equivalent" simpliciter — that is the entire content of the antitonicity
results.
-/

namespace Integration.Experiment.ObservationalEquivalence

open Set

/-! ## §1 Theories, languages, equivalence -/

/-- **A theory, viewed through an experimental interface**: for each experiment
`e : E` it declares the set of outcomes it permits.  This is deliberately the
weakest possible notion — no parameters, no dynamics, no probability — because
it is the level at which empirical equivalence is a meaningful question. -/
structure Theory (E : Type*) (O : Type*) where
  /-- The outcomes the theory permits for the given experiment. -/
  Pred : E → Set O

variable {E O : Type*}

/-- **Observational equivalence relative to an experiment language `L`.** -/
def ObsEquiv (L : Set E) (H₁ H₂ : Theory E O) : Prop :=
  ∀ e ∈ L, H₁.Pred e = H₂.Pred e

theorem obsEquiv_refl (L : Set E) (H : Theory E O) : ObsEquiv L H H := fun _ _ => rfl

theorem obsEquiv_symm {L : Set E} {H₁ H₂ : Theory E O} (h : ObsEquiv L H₁ H₂) :
    ObsEquiv L H₂ H₁ := fun e he => (h e he).symm

theorem obsEquiv_trans {L : Set E} {H₁ H₂ H₃ : Theory E O}
    (h₁ : ObsEquiv L H₁ H₂) (h₂ : ObsEquiv L H₂ H₃) : ObsEquiv L H₁ H₃ :=
  fun e he => (h₁ e he).trans (h₂ e he)

theorem obsEquiv_equivalence (L : Set E) :
    Equivalence (ObsEquiv (O := O) L) :=
  ⟨obsEquiv_refl L, obsEquiv_symm, obsEquiv_trans⟩

/-- With no experiments available, nothing is distinguishable. -/
@[simp] theorem obsEquiv_empty (H₁ H₂ : Theory E O) : ObsEquiv (∅ : Set E) H₁ H₂ := by
  intro e he; exact absurd he (notMem_empty e)

/-- Equivalence for the full language is equality of the whole interface. -/
theorem obsEquiv_univ_iff {H₁ H₂ : Theory E O} :
    ObsEquiv (univ : Set E) H₁ H₂ ↔ H₁ = H₂ := by
  constructor
  · intro h
    cases H₁; cases H₂
    simp only [Theory.mk.injEq]
    exact funext fun e => h e (mem_univ e)
  · rintro rfl _ _; rfl

/-- **A larger language is a finer relation.**  Extending the set of available
experiments can only *remove* equivalences, never create them. -/
theorem obsEquiv_antitone {L₁ L₂ : Set E} (hL : L₁ ⊆ L₂) {H₁ H₂ : Theory E O}
    (h : ObsEquiv L₂ H₁ H₂) : ObsEquiv L₁ H₁ H₂ :=
  fun e he => h e (hL he)

/-- The observational equivalence class of a theory relative to `L`. -/
def obsClass (L : Set E) (H : Theory E O) : Set (Theory E O) :=
  {H' | ObsEquiv L H H'}

@[simp] theorem mem_obsClass {L : Set E} {H H' : Theory E O} :
    H' ∈ obsClass L H ↔ ObsEquiv L H H' := Iff.rfl

theorem self_mem_obsClass (L : Set E) (H : Theory E O) : H ∈ obsClass L H :=
  obsEquiv_refl L H

/-- **New experiments refine the observational equivalence classes of theories.**
This is the formal content of "scientific progress" in this setting: growing the
experiment language shrinks every class. -/
theorem obsClass_antitone {L₁ L₂ : Set E} (hL : L₁ ⊆ L₂) (H : Theory E O) :
    obsClass L₂ H ⊆ obsClass L₁ H :=
  fun _ h => obsEquiv_antitone hL h

/-! ## §2 Separating experiments -/

/-- Experiment `e` **separates** two theories when they permit different
outcomes for it. -/
def Separates (e : E) (H₁ H₂ : Theory E O) : Prop := H₁.Pred e ≠ H₂.Pred e

/-- Inequivalence relative to `L` is exactly the existence of a separating
experiment *inside* `L`. -/
theorem not_obsEquiv_iff_exists_separating {L : Set E} {H₁ H₂ : Theory E O} :
    ¬ ObsEquiv L H₁ H₂ ↔ ∃ e ∈ L, Separates e H₁ H₂ := by
  unfold ObsEquiv Separates
  push_neg
  rfl

theorem separates_symm {e : E} {H₁ H₂ : Theory E O} (h : Separates e H₁ H₂) :
    Separates e H₂ H₁ := fun hh => h hh.symm

/-- A separating experiment must lie outside any language for which the two
theories are equivalent. -/
theorem separating_not_mem_of_obsEquiv {L : Set E} {H₁ H₂ : Theory E O}
    (h : ObsEquiv L H₁ H₂) {e : E} (hs : Separates e H₁ H₂) : e ∉ L :=
  fun he => hs (h e he)

/-! ## §3 Equivalent theories are the same scientific object inside `L` -/

/-- A theory is **refuted** by an experiment when the observed outcome is not
among the outcomes it permits. -/
def Refutes (e : E) (o : O) (H : Theory E O) : Prop := o ∉ H.Pred e

/-- **Refutation transfers across observational equivalence.**  Inside `L`, two
`L`-equivalent theories cannot be told apart even by failure. -/
theorem obsEquiv_transfers_refutation {L : Set E} {H₁ H₂ : Theory E O}
    (h : ObsEquiv L H₁ H₂) {e : E} (he : e ∈ L) {o : O} (hr : Refutes e o H₁) :
    Refutes e o H₂ := by
  unfold Refutes at hr ⊢
  rwa [← h e he]

/-- And so does survival. -/
theorem obsEquiv_transfers_survival {L : Set E} {H₁ H₂ : Theory E O}
    (h : ObsEquiv L H₁ H₂) {e : E} (he : e ∈ L) {o : O} (hs : o ∈ H₁.Pred e) :
    o ∈ H₂.Pred e := by
  rwa [← h e he]

/-! ## §4 The RC circuit as a worked splitting example

The RC specimen of `Integration.Experiment.RCCircuit` gives the cleanest
possible instance: in the language of *voltage samples* the pairs `(R, C)` and
`(2R, C/2)` are observationally equivalent, and adding one resistance
measurement to the language splits them. -/

/-- The RC experiment interface: sample the voltage at a time, or read the
resistance off an ohmmeter. -/
inductive RCExp where
  /-- Sample the capacitor voltage at time `t`. -/
  | volt (t : ℝ) : RCExp
  /-- Measure the resistance directly. -/
  | ohm : RCExp

/-- The language containing only voltage samples. -/
def voltOnly : Set RCExp := {e | ∃ t, e = RCExp.volt t}

/-- The language that also has an ohmmeter. -/
def voltAndOhm : Set RCExp := univ

theorem voltOnly_subset_voltAndOhm : voltOnly ⊆ voltAndOhm := fun _ _ => mem_univ _

theorem ohm_not_mem_voltOnly : RCExp.ohm ∉ voltOnly := by
  rintro ⟨t, ht⟩
  exact RCExp.noConfusion ht

/-- The theory asserted by a specific `(R, C)` pair: the voltage sample is
predicted exactly by the closed-form solution, and the ohmmeter reads `R`. -/
noncomputable def rcTheory (Vin V0 R C : ℝ) : Theory RCExp ℝ where
  Pred
    | RCExp.volt t => {RCCircuit.voltage Vin V0 R C t}
    | RCExp.ohm => {R}

@[simp] theorem rcTheory_volt (Vin V0 R C t : ℝ) :
    (rcTheory Vin V0 R C).Pred (RCExp.volt t) = {RCCircuit.voltage Vin V0 R C t} := rfl

@[simp] theorem rcTheory_ohm (Vin V0 R C : ℝ) :
    (rcTheory Vin V0 R C).Pred RCExp.ohm = {R} := rfl

/-- **In the voltage-sample language, `(R, C)` and `(2R, C/2)` are
observationally equivalent.**  This is the theory-level shadow of
`RCCircuit.perfect_measurements_do_not_identify_R_and_C`: the failure is not
that the data were insufficient, it is that the two theories are the same
object for this experimental language. -/
theorem rc_theories_equivalent_for_voltage_only (Vin V0 R C : ℝ) :
    ObsEquiv voltOnly (rcTheory Vin V0 R C) (rcTheory Vin V0 (2 * R) (C / 2)) := by
  rintro e ⟨t, rfl⟩
  simp only [rcTheory_volt]
  rw [RCCircuit.voltage_depends_only_on_the_product Vin V0 R C (2 * R) (C / 2) (by ring) t]

/-- The ohmmeter is a separating experiment. -/
theorem ohm_separates {R : ℝ} (hR : R ≠ 0) (Vin V0 C : ℝ) :
    Separates RCExp.ohm (rcTheory Vin V0 R C) (rcTheory Vin V0 (2 * R) (C / 2)) := by
  simp only [Separates, rcTheory_ohm, ne_eq, singleton_eq_singleton_iff]
  intro h
  exact hR (by linarith)

/-- **Extending the experiment language splits the class.**  The pair
`(2R, C/2)` lies in the voltage-only class of `(R, C)` but not in its class for
the extended language.  Both directions of the roadmap slogan are visible here:
the class genuinely shrinks, and it shrinks because a *new experiment* was
added, not because more of the old data were collected. -/
theorem ohmmeter_splits_the_class {R : ℝ} (hR : R ≠ 0) (Vin V0 C : ℝ) :
    rcTheory Vin V0 (2 * R) (C / 2) ∈ obsClass voltOnly (rcTheory Vin V0 R C) ∧
      rcTheory Vin V0 (2 * R) (C / 2) ∉ obsClass voltAndOhm (rcTheory Vin V0 R C) := by
  refine ⟨rc_theories_equivalent_for_voltage_only Vin V0 R C, ?_⟩
  intro h
  exact ohm_separates hR Vin V0 C (h RCExp.ohm (mem_univ _))

/-- The classes are therefore *strictly* nested: antitonicity is not vacuous. -/
theorem obsClass_strictly_shrinks {R : ℝ} (hR : R ≠ 0) (Vin V0 C : ℝ) :
    obsClass voltAndOhm (rcTheory Vin V0 R C) ⊂ obsClass voltOnly (rcTheory Vin V0 R C) := by
  refine ⟨obsClass_antitone voltOnly_subset_voltAndOhm _, ?_⟩
  intro hsub
  obtain ⟨hin, hout⟩ := ohmmeter_splits_the_class hR Vin V0 C
  exact hout (hsub hin)

/-- **Negative: observational equivalence does not identify theories.**  The two
RC theories are equivalent for the voltage-only language and are nevertheless
different theories.  Nothing in this development licenses reading `∼_L` as
"the same theory". -/
theorem equivalent_theories_need_not_be_equal {R : ℝ} (hR : R ≠ 0) (Vin V0 C : ℝ) :
    ObsEquiv voltOnly (rcTheory Vin V0 R C) (rcTheory Vin V0 (2 * R) (C / 2)) ∧
      rcTheory Vin V0 R C ≠ rcTheory Vin V0 (2 * R) (C / 2) := by
  refine ⟨rc_theories_equivalent_for_voltage_only Vin V0 R C, ?_⟩
  intro h
  exact ohm_separates hR Vin V0 C (by rw [h])

/-! ## §5 Discriminating a whole family, and a negative about design -/

/-- Experiment `e` **discriminates** a finite family of theories when it assigns
them pairwise different outcome sets. -/
def Discriminates (e : E) {n : ℕ} (H : Fin n → Theory E O) : Prop :=
  Function.Injective fun i => (H i).Pred e

/-- A discriminating experiment separates every pair. -/
theorem separates_of_discriminates {e : E} {n : ℕ} {H : Fin n → Theory E O}
    (h : Discriminates e H) {i j : Fin n} (hij : i ≠ j) : Separates e (H i) (H j) :=
  fun hh => hij (h hh)

/-- Three theories over a two-experiment language, used for the negative below:
theory `i` predicts the single outcome `discFamilyValue i e`. -/
def discFamilyValue : Fin 3 → Fin 2 → ℕ := ![![0, 0], ![0, 1], ![1, 0]]

/-- The three theories of the counterexample family. -/
def discFamily (i : Fin 3) : Theory (Fin 2) ℕ where
  Pred := fun e => {discFamilyValue i e}

/-- **Negative: pairwise separability does not give one discriminating
experiment.**  Every pair of the three theories is separated by some experiment
of the language, yet no single experiment tells all three apart.  So "choose the
experiment that separates the candidates" is not in general satisfiable by one
measurement, and experiment design over a *family* of theories is strictly
harder than pairwise discrimination. -/
theorem pairwise_separation_does_not_give_one_discriminating_experiment :
    (∀ i j : Fin 3, i ≠ j → ∃ e : Fin 2, Separates e (discFamily i) (discFamily j)) ∧
      ¬ ∃ e : Fin 2, Discriminates e discFamily := by
  have hval : ∀ (i : Fin 3) (e : Fin 2) (j : Fin 3),
      (discFamily i).Pred e = (discFamily j).Pred e ↔
        discFamilyValue i e = discFamilyValue j e := by
    intro i e j
    simp [discFamily, Set.singleton_eq_singleton_iff]
  constructor
  · intro i j hij
    by_contra hcon
    push_neg at hcon
    have h0 := hcon 0
    have h1 := hcon 1
    simp only [Separates, not_not] at h0 h1
    rw [hval] at h0 h1
    apply hij
    revert h0 h1
    fin_cases i <;> fin_cases j <;> simp [discFamilyValue]
  · rintro ⟨e, he⟩
    fin_cases e
    · have : (0 : Fin 3) = 1 := by
        refine he ?_
        simp [discFamily, discFamilyValue]
      exact absurd this (by decide)
    · have : (0 : Fin 3) = 2 := by
        refine he ?_
        simp [discFamily, discFamilyValue]
      exact absurd this (by decide)

end Integration.Experiment.ObservationalEquivalence
