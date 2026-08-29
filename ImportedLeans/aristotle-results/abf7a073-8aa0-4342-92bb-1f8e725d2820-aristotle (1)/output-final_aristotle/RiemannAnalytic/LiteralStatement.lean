/-
Literal statements and verified reductions for the Riemann Hypothesis.

Nothing in this file is schematic: `riemannZeta` and `completedRiemannZeta`
are Mathlib's genuine analytic objects, and `RiemannHypothesis` is Mathlib's
literal formulation of the conjecture.  What is proved here is the exact
reduction of that literal statement to the completed (`Λ`) form, together with
the localisation of all zeros of `Λ` to the open critical strip.

The Riemann Hypothesis itself is *not* proved here, and no result in this file
assumes it.
-/
import Mathlib

namespace RiemannAnalytic

open Complex

/-- The Riemann Hypothesis in completed form: every zero of the completed zeta
function `Λ` lies on the critical line. -/
def CompletedRiemannHypothesis : Prop :=
  ∀ s : ℂ, completedRiemannZeta s = 0 → s.re = 1 / 2

/-- The completed zeta function has no zero in the closed half-plane `re s ≥ 1`. -/
theorem completedZeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    completedRiemannZeta s ≠ 0 := by
  intro h
  have hs0 : s ≠ 0 := by
    intro hzero
    rw [hzero] at hs
    norm_num at hs
  have : riemannZeta s = 0 := by rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]
  exact riemannZeta_ne_zero_of_one_le_re hs this

/-- The completed zeta function has no zero in the closed half-plane `re s ≤ 0`;
this follows from the previous statement and the functional equation. -/
theorem completedZeta_ne_zero_of_re_le_zero {s : ℂ} (hs : s.re ≤ 0) :
    completedRiemannZeta s ≠ 0 := by
  intro h
  have hre : 1 ≤ (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  exact completedZeta_ne_zero_of_one_le_re hre (by rw [completedRiemannZeta_one_sub]; exact h)

/-- Every zero of the completed zeta function lies in the open critical strip. -/
theorem completedZeta_zero_mem_strip {s : ℂ} (h : completedRiemannZeta s = 0) :
    0 < s.re ∧ s.re < 1 := by
  constructor
  · by_contra hcon
    exact completedZeta_ne_zero_of_re_le_zero (not_lt.1 hcon) h
  · by_contra hcon
    exact completedZeta_ne_zero_of_one_le_re (not_lt.1 hcon) h

/-- The zero set of `Λ` is symmetric under `s ↦ 1 - s`. -/
theorem completedZeta_zero_reflect {s : ℂ} (h : completedRiemannZeta s = 0) :
    completedRiemannZeta (1 - s) = 0 := by
  rw [completedRiemannZeta_one_sub]; exact h

/-- Because of the reflection symmetry, the completed Riemann Hypothesis is
equivalent to the one-sided statement that `Λ` has no zero to the right of the
critical line. -/
theorem completedRH_iff_no_zero_right :
    CompletedRiemannHypothesis ↔ ∀ s : ℂ, completedRiemannZeta s = 0 → s.re ≤ 1 / 2 := by
  constructor
  · intro hRH s hs
    exact le_of_eq (hRH s hs)
  · intro hhalf s hs
    have h1 : s.re ≤ 1 / 2 := hhalf s hs
    have h2 : (1 - s).re ≤ 1 / 2 := hhalf _ (completedZeta_zero_reflect hs)
    simp only [Complex.sub_re, Complex.one_re] at h2
    linarith

/-- **Reduction of the literal Riemann Hypothesis to the completed form.**
Mathlib's `RiemannHypothesis` — every zero of `riemannZeta` other than the
trivial zeros and the pole at `1` has real part `1/2` — follows from
`CompletedRiemannHypothesis`. -/
theorem riemannHypothesis_of_completed (h : CompletedRiemannHypothesis) :
    RiemannHypothesis := by
  intro s hzero htriv _
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs, riemannZeta_zero] at hzero
    norm_num at hzero
  by_cases hG : Gammaℝ s = 0
  · exfalso
    obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.1 hG
    match n, hn with
    | 0, hn => exact hs0 (by simpa using hn)
    | (m + 1), hn =>
      refine htriv ⟨m, ?_⟩
      rw [hn]
      push_cast
      ring
  · refine h s ?_
    rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hzero
    exact hzero.resolve_right hG

/-- Conversely, the completed Riemann Hypothesis follows from Mathlib's literal
`RiemannHypothesis`; so the two formulations are equivalent. -/
theorem completed_of_riemannHypothesis (h : RiemannHypothesis) :
    CompletedRiemannHypothesis := by
  intro s hs
  obtain ⟨hlow, hhigh⟩ := completedZeta_zero_mem_strip hs
  have hs0 : s ≠ 0 := by
    intro hz
    rw [hz] at hlow
    simp at hlow
  have hzeta : riemannZeta s = 0 := by
    rw [riemannZeta_def_of_ne_zero hs0, hs, zero_div]
  refine h s hzeta ?_ ?_
  · rintro ⟨n, rfl⟩
    have : ((-2 * ((n : ℂ) + 1)).re) = -2 * ((n : ℝ) + 1) := by
      simp
    rw [this] at hlow
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  · intro hone
    rw [hone] at hhigh
    simp at hhigh

/-- The literal Riemann Hypothesis is equivalent to its completed form. -/
theorem riemannHypothesis_iff_completed :
    RiemannHypothesis ↔ CompletedRiemannHypothesis :=
  ⟨completed_of_riemannHypothesis, riemannHypothesis_of_completed⟩

/-- The literal Riemann Hypothesis is equivalent to the purely one-sided
statement that the completed zeta function has no zero strictly to the right of
the critical line. -/
theorem riemannHypothesis_iff_no_completed_zero_right :
    RiemannHypothesis ↔ ∀ s : ℂ, completedRiemannZeta s = 0 → s.re ≤ 1 / 2 :=
  riemannHypothesis_iff_completed.trans completedRH_iff_no_zero_right

end RiemannAnalytic
