/-
# Nonvanishing of a `cosh` combination at large argument

The three-taper stage needs a *nonvanishing* statement rather than a sign: a
`3 × 3` leading determinant that is merely nonzero already produces the exact
elimination of two nuisance zeros.  The determinant, read as a function of the last
window centre, is a combination

    α₀ + α₁ cosh(a₁ c) + α₂ cosh(a₂ c) + α₃ cosh(a₃ c),

and this module proves the only fact needed about such combinations: if the `aᵢ` are
distinct positive heights and the coefficients are not all zero, then the combination
is nonzero at arbitrarily large `c`.

The proof is the elementary asymptotic one — divide by `cosh(a_j c)` for the largest
index `j` with `α_j ≠ 0` and use `cosh(a c)/cosh(b c) → 0` for `0 ≤ a < b`, which is
itself immediate from `e^x/2 ≤ cosh x ≤ e^x` on `x ≥ 0`.

No `sorry`, no `axiom`, no numerical evidence.
-/
import Mathlib

noncomputable section

open Filter Topology

namespace Zeta23Bridge
namespace CoshCombinationSeparation

/-! ## The ratio of two `cosh` scalings -/

theorem cosh_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : Real.cosh x ≤ Real.exp x := by
  rw [Real.cosh_eq]
  have h : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  linarith

theorem exp_div_two_le_cosh (x : ℝ) : Real.exp x / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  have h : 0 < Real.exp (-x) := Real.exp_pos _
  linarith

/-- `cosh(a c)/cosh(b c) → 0` as `c → ∞`, for `0 ≤ a < b`. -/
theorem tendsto_cosh_div_cosh {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Tendsto (fun c : ℝ => Real.cosh (a * c) / Real.cosh (b * c)) atTop (𝓝 0) := by
  have hexp : Tendsto (fun c : ℝ => 2 * Real.exp ((a - b) * c)) atTop (𝓝 0) := by
    have hlin : Tendsto (fun c : ℝ => (a - b) * c) atTop atBot := by
      have hneg : a - b < 0 := by linarith
      exact (tendsto_const_mul_atBot_of_neg hneg).mpr tendsto_id
    have := Real.tendsto_exp_atBot.comp hlin
    simpa using this.const_mul (2 : ℝ)
  refine squeeze_zero' ?_ ?_ hexp
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with c hc
    exact le_of_lt (div_pos (Real.cosh_pos _) (Real.cosh_pos _))
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with c hc
    have hac : 0 ≤ a * c := mul_nonneg ha hc
    have h1 : Real.cosh (a * c) ≤ Real.exp (a * c) := cosh_le_exp_of_nonneg hac
    have h2 : Real.exp (b * c) / 2 ≤ Real.cosh (b * c) := exp_div_two_le_cosh _
    have h3 : (0:ℝ) < Real.exp (b * c) / 2 := by positivity
    have h4 : Real.cosh (a * c) / Real.cosh (b * c)
        ≤ Real.exp (a * c) / (Real.exp (b * c) / 2) :=
      div_le_div₀ (Real.exp_pos _).le h1 h3 h2
    have h5 : Real.exp (a * c) / (Real.exp (b * c) / 2) = 2 * Real.exp ((a - b) * c) := by
      rw [show (a - b) * c = a * c - b * c by ring, Real.exp_sub]
      field_simp
    linarith [h4, h5.le, h5.ge]

/-- `1/cosh(b c) → 0` as `c → ∞`, for `0 < b`. -/
theorem tendsto_inv_cosh {b : ℝ} (hb : 0 < b) :
    Tendsto (fun c : ℝ => 1 / Real.cosh (b * c)) atTop (𝓝 0) := by
  have h := tendsto_cosh_div_cosh (a := 0) (b := b) le_rfl hb
  simpa using h

/-! ## Nonvanishing at arbitrarily large argument -/

/-- If `f c / cosh(b c)` has a nonzero limit, then `f` is nonzero at arbitrarily large
arguments. -/
theorem exists_gt_ne_zero_of_tendsto_div {b L : ℝ} {f : ℝ → ℝ}
    (hf : Tendsto (fun c : ℝ => f c / Real.cosh (b * c)) atTop (𝓝 L)) (hL : L ≠ 0) (C : ℝ) :
    ∃ c : ℝ, C < c ∧ f c ≠ 0 := by
  have hev : ∀ᶠ c in atTop, f c / Real.cosh (b * c) ≠ 0 := hf.eventually_ne hL
  obtain ⟨c, hc, hcne⟩ := ((hev.and (eventually_gt_atTop C)).exists)
  exact ⟨c, hcne, fun h => hc (by rw [h]; simp)⟩

/-- **The combination is nonzero at arbitrarily large argument.**  For three distinct
positive heights and coefficients that are not all zero, the combination
`α₀ + α₁ cosh(a₁ c) + α₂ cosh(a₂ c) + α₃ cosh(a₃ c)` is nonzero at some `c` beyond every
prescribed bound. -/
theorem exists_gt_coshCombo_ne_zero {a₁ a₂ a₃ al0 al1 al2 al3 : ℝ}
    (ha₁ : 0 < a₁) (h₁₂ : a₁ < a₂) (h₂₃ : a₂ < a₃)
    (hne : al1 ≠ 0 ∨ al2 ≠ 0 ∨ al3 ≠ 0) (C : ℝ) :
    ∃ c : ℝ, C < c ∧
      al0 + al1 * Real.cosh (a₁ * c) + al2 * Real.cosh (a₂ * c)
        + al3 * Real.cosh (a₃ * c) ≠ 0 := by
  have ha₂ : 0 < a₂ := ha₁.trans h₁₂
  have ha₃ : 0 < a₃ := ha₂.trans h₂₃
  by_cases h3 : al3 ≠ 0
  · refine exists_gt_ne_zero_of_tendsto_div (b := a₃) (L := al3)
      (f := fun c => al0 + al1 * Real.cosh (a₁ * c) + al2 * Real.cosh (a₂ * c)
        + al3 * Real.cosh (a₃ * c)) ?_ h3 C
    have hrw : (fun c : ℝ => (al0 + al1 * Real.cosh (a₁ * c) + al2 * Real.cosh (a₂ * c)
          + al3 * Real.cosh (a₃ * c)) / Real.cosh (a₃ * c))
        = fun c : ℝ => al0 * (1 / Real.cosh (a₃ * c))
          + al1 * (Real.cosh (a₁ * c) / Real.cosh (a₃ * c))
          + al2 * (Real.cosh (a₂ * c) / Real.cosh (a₃ * c)) + al3 := by
      funext c
      have hpos : Real.cosh (a₃ * c) ≠ 0 := ne_of_gt (Real.cosh_pos _)
      field_simp
    rw [hrw]
    have t0 := (tendsto_inv_cosh ha₃).const_mul al0
    have t1 := (tendsto_cosh_div_cosh (a := a₁) (b := a₃) ha₁.le (h₁₂.trans h₂₃)).const_mul al1
    have t2 := (tendsto_cosh_div_cosh (a := a₂) (b := a₃) ha₂.le h₂₃).const_mul al2
    have h := ((t0.add t1).add t2).add_const al3
    simp only [mul_zero, add_zero, zero_add] at h
    exact h
  · push_neg at h3
    subst h3
    by_cases h2 : al2 ≠ 0
    · refine exists_gt_ne_zero_of_tendsto_div (b := a₂) (L := al2)
        (f := fun c => al0 + al1 * Real.cosh (a₁ * c) + al2 * Real.cosh (a₂ * c)
          + 0 * Real.cosh (a₃ * c)) ?_ h2 C
      have hrw : (fun c : ℝ => (al0 + al1 * Real.cosh (a₁ * c) + al2 * Real.cosh (a₂ * c)
            + 0 * Real.cosh (a₃ * c)) / Real.cosh (a₂ * c))
          = fun c : ℝ => al0 * (1 / Real.cosh (a₂ * c))
            + al1 * (Real.cosh (a₁ * c) / Real.cosh (a₂ * c)) + al2 := by
        funext c
        have hpos : Real.cosh (a₂ * c) ≠ 0 := ne_of_gt (Real.cosh_pos _)
        field_simp
        ring
      rw [hrw]
      have t0 := (tendsto_inv_cosh ha₂).const_mul al0
      have t1 := (tendsto_cosh_div_cosh (a := a₁) (b := a₂) ha₁.le h₁₂).const_mul al1
      have h := (t0.add t1).add_const al2
      simp only [mul_zero, add_zero, zero_add] at h
      exact h
    · push_neg at h2
      subst h2
      have h1 : al1 ≠ 0 := by
        rcases hne with h | h | h
        · exact h
        · exact absurd rfl h
        · exact absurd rfl h
      refine exists_gt_ne_zero_of_tendsto_div (b := a₁) (L := al1)
        (f := fun c => al0 + al1 * Real.cosh (a₁ * c) + 0 * Real.cosh (a₂ * c)
          + 0 * Real.cosh (a₃ * c)) ?_ h1 C
      have hrw : (fun c : ℝ => (al0 + al1 * Real.cosh (a₁ * c) + 0 * Real.cosh (a₂ * c)
            + 0 * Real.cosh (a₃ * c)) / Real.cosh (a₁ * c))
          = fun c : ℝ => al0 * (1 / Real.cosh (a₁ * c)) + al1 := by
        funext c
        have hpos : Real.cosh (a₁ * c) ≠ 0 := ne_of_gt (Real.cosh_pos _)
        field_simp
        ring
      rw [hrw]
      have t0 := (tendsto_inv_cosh ha₁).const_mul al0
      have h := t0.add_const al1
      simp only [mul_zero, zero_add] at h
      exact h

end CoshCombinationSeparation
end Zeta23Bridge
