import Mathlib
import Integration.Experiment.ObservationalEquivalence

/-!
# Stage 9 seed — competing theories as experiment-generating families

`Integration.Experiment.ObservationalEquivalence` gives the generic vocabulary:
theories compared through the observable distinctions they force, relative to an
experiment language `L`.  This file instantiates it on the shape the roadmap
asks for at the fundamental-theory end:

```
H₀ = baseline
H₁ = baseline + candidate correction A
H₂ = baseline + candidate correction B
```

with an experiment parameterised by a scalar setting (read it as an energy) and
predictions `yᵢ(E)`.  The corrections are `α E²` and `β E³`: same baseline, same
observable, different leading behaviour.

The point is that the discrimination question

> which measurement setting maximally separates `H₀`, `H₁`, `H₂`?

is here *the same mathematical question* as choosing an RC sampling time, and it
has a proved answer of the expected shape:

* **at `E = 0` the three theories are observationally identical** — a language
  containing only that setting cannot distinguish any of them;
* **at almost every other setting a single experiment separates all three** —
  the exceptions are exactly `E = 0` and the crossing point `E = α/β`, and both
  exceptions are proved to be genuine.

## Claim boundary

`baseline`, `α` and `β` are declared functions and constants.  Nothing here is a
statement about general relativity, quantum field theory, or any physical
correction: the file proves facts about three declared prediction maps, and the
labels `H₀`, `H₁`, `H₂` are comments.  "Separates" means the predicted outcome
sets differ; no probability, no likelihood ratio and no test is involved.
-/

namespace Integration.Experiment.CandidateCorrections

open Set
open Integration.Experiment.ObservationalEquivalence

/-! ## §1 The three candidates -/

/-- A theory that predicts the baseline plus a declared correction, exactly, at
each experimental setting. -/
def correctedTheory (baseline corr : ℝ → ℝ) : Theory ℝ ℝ where
  Pred := fun e => {baseline e + corr e}

@[simp] theorem correctedTheory_pred (baseline corr : ℝ → ℝ) (e : ℝ) :
    (correctedTheory baseline corr).Pred e = {baseline e + corr e} := rfl

variable (baseline : ℝ → ℝ) (a b : ℝ)

/-- `H₀`, `H₁`, `H₂`: the baseline, the baseline with an `α E²` correction, and
the baseline with a `β E³` correction. -/
def candidates : Fin 3 → Theory ℝ ℝ :=
  ![correctedTheory baseline (fun _ => 0),
    correctedTheory baseline (fun e => a * e ^ 2),
    correctedTheory baseline (fun e => b * e ^ 3)]

@[simp] theorem candidates_zero :
    candidates baseline a b 0 = correctedTheory baseline (fun _ => 0) := rfl

@[simp] theorem candidates_one :
    candidates baseline a b 1 = correctedTheory baseline (fun e => a * e ^ 2) := rfl

@[simp] theorem candidates_two :
    candidates baseline a b 2 = correctedTheory baseline (fun e => b * e ^ 3) := rfl

/-! ## §2 A language that cannot see the difference -/

/-- The experiment language consisting of the single setting `E = 0`. -/
def zeroOnly : Set ℝ := {0}

/-- **At `E = 0` the corrections are invisible**: all three candidates predict
the same outcome, so a language containing only that setting collapses them into
one observational equivalence class. -/
theorem candidates_collapse_at_zero (i j : Fin 3) :
    ObsEquiv zeroOnly (candidates baseline a b i) (candidates baseline a b j) := by
  intro e he
  rw [show e = 0 from he]
  fin_cases i <;> fin_cases j <;> simp

/-! ## §3 A setting that separates all three -/

/-- **A single experiment discriminates all three candidates**, provided the
setting is nonzero, both corrections are nonzero, and the setting is not the
crossing point `α/β` where the two corrections happen to agree. -/
theorem energy_discriminates {e : ℝ} (he : e ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcross : a * e ^ 2 ≠ b * e ^ 3) :
    Discriminates e (candidates baseline a b) := by
  have h1 : baseline e + 0 ≠ baseline e + a * e ^ 2 := by
    simp only [ne_eq, add_right_inj]
    exact fun h => (mul_ne_zero ha (pow_ne_zero 2 he)) h.symm
  have h2 : baseline e + 0 ≠ baseline e + b * e ^ 3 := by
    simp only [ne_eq, add_right_inj]
    exact fun h => (mul_ne_zero hb (pow_ne_zero 3 he)) h.symm
  have h3 : baseline e + a * e ^ 2 ≠ baseline e + b * e ^ 3 := by
    simpa using hcross
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp [candidates, correctedTheory] at hij ⊢ <;>
    first
      | rfl
      | exact absurd hij hcross
      | exact absurd hij.symm hcross
      | (rcases hij with h | h) <;> simp_all

/-- The crossing point is real: at `e = α/β` the two corrections coincide, so
that one setting cannot tell `H₁` from `H₂` however large it is. -/
theorem crossing_point_fails (hb : b ≠ 0) :
    ¬ Separates (a / b) (candidates baseline a b 1) (candidates baseline a b 2) := by
  intro h
  apply h
  simp only [candidates_one, candidates_two, correctedTheory_pred, singleton_eq_singleton_iff]
  field_simp

/-! ## §4 Extending the language splits the class -/

/-- The language with the useless setting `0` and one informative setting `e`. -/
def withEnergy (e : ℝ) : Set ℝ := {0, e}

theorem zeroOnly_subset_withEnergy (e : ℝ) : zeroOnly ⊆ withEnergy e := by
  rintro x rfl
  exact Or.inl rfl

/-- **Adding one informative setting splits the class.**  `H₁` sits in the
observational equivalence class of `H₀` for the zero-only language and leaves it
as soon as the language contains a separating setting.  This is the
fundamental-theory instance of
`ObservationalEquivalence.obsClass_antitone`: extending the experiment language
refines the equivalence classes of theories. -/
theorem new_setting_splits_the_class {e : ℝ} (he : e ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcross : a * e ^ 2 ≠ b * e ^ 3) :
    candidates baseline a b 1 ∈ obsClass zeroOnly (candidates baseline a b 0) ∧
      candidates baseline a b 1 ∉ obsClass (withEnergy e) (candidates baseline a b 0) := by
  refine ⟨candidates_collapse_at_zero baseline a b 0 1, ?_⟩
  intro hmem
  have hsep : Separates e (candidates baseline a b 0) (candidates baseline a b 1) :=
    separates_of_discriminates (energy_discriminates baseline a b he ha hb hcross)
      (by decide : (0 : Fin 3) ≠ 1)
  exact hsep (hmem e (Or.inr rfl))

/-- Hence the class strictly shrinks: the experiment language is what carries
the discriminating power, not the theories. -/
theorem obsClass_strictly_shrinks_with_energy {e : ℝ} (he : e ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcross : a * e ^ 2 ≠ b * e ^ 3) :
    obsClass (withEnergy e) (candidates baseline a b 0) ⊂
      obsClass zeroOnly (candidates baseline a b 0) := by
  refine ⟨obsClass_antitone (zeroOnly_subset_withEnergy e) _, ?_⟩
  intro hsub
  obtain ⟨hin, hout⟩ := new_setting_splits_the_class baseline a b he ha hb hcross
  exact hout (hsub hin)

end Integration.Experiment.CandidateCorrections
