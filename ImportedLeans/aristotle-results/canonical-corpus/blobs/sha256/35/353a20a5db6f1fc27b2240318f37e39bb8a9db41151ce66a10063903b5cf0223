/-
**G12 — the literal capstone in *relative* form.**

`LiteralRoute.riemannHypothesis_of_defect_exceeds_error` records the terminal
step of the route in its *absolute* form: floor beats budget.  G10 proved
(`RelativeContraction.absolute_budget_insufficient`) that an absolute budget can
never force the displacement to vanish, so the terminal step the programme
actually needs is the *relative* one.  This file supplies it at literal
strength, against Mathlib's `RiemannHypothesis`:

* `zero_on_critical_line_of_relative_contraction` — for a single zero of the
  completed zeta function, the geometric floor plus a strictly contractive
  relative budget forces `Re ρ = 1/2` **exactly**, with no tube and no limiting
  argument;

* `riemannHypothesis_of_relative_contraction` — the same hypotheses for every
  zero give Mathlib's literal `RiemannHypothesis`;

* `riemannHypothesis_of_relative_parts` — the packaged four-budget form
  (prime, tail, mixed interference, endpoint) demanded by the programme: if the
  four relative budgets sum to less than `1` at every zero, the Riemann
  Hypothesis follows.

Every hypothesis here is an explicit input.  **Nothing in this file proves any
of them**, and in particular nothing here proves the Riemann Hypothesis; the
missing input remains the relative prime budget `η_prime < 1`.
-/
import RiemannAnalytic.LiteralRoute
import RiemannAnalytic.RelativeContraction

namespace RiemannAnalytic

open Complex

/-- **Exact critical-line localisation of a single zero.**  A defect obeying the
geometric floor `cL⁶α² ≤ D` and a strictly contractive relative budget
`D ≤ ηD`, `η < 1`, forces the zero onto the critical line exactly. -/
theorem zero_on_critical_line_of_relative_contraction {c L D eta : ℝ} {ρ : ℂ}
    (hc : 0 < c) (hL : 0 < L) (hD : 0 ≤ D) (heta : eta < 1)
    (hfloor : c * L ^ 6 * zeroOffset ρ ^ 2 ≤ D)
    (hcontract : D ≤ eta * D) :
    ρ.re = 1 / 2 := by
  have hzero : zeroOffset ρ = 0 :=
    offLineTarget_excluded_of_relative_budget hc hL hD heta hfloor hcontract
  unfold zeroOffset at hzero
  linarith

/-- **The literal relative capstone.**  If every zero of the completed zeta
function carries a nonnegative defect obeying the geometric floor and a strictly
contractive relative budget, then Mathlib's `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_relative_contraction {c : ℝ} (hc : 0 < c)
    (L D eta : ℂ → ℝ)
    (hL : ∀ ρ : ℂ, 0 < L ρ)
    (hD : ∀ ρ : ℂ, completedRiemannZeta ρ = 0 → 0 ≤ D ρ)
    (hfloor : ∀ ρ : ℂ, completedRiemannZeta ρ = 0 →
      c * L ρ ^ 6 * zeroOffset ρ ^ 2 ≤ D ρ)
    (heta : ∀ ρ : ℂ, completedRiemannZeta ρ = 0 → eta ρ < 1)
    (hcontract : ∀ ρ : ℂ, completedRiemannZeta ρ = 0 → D ρ ≤ eta ρ * D ρ) :
    RiemannHypothesis := by
  refine hermitianRoute_riemannHypothesis fun ρ hρ hre => ?_
  have hhalf : ρ.re = 1 / 2 :=
    zero_on_critical_line_of_relative_contraction hc (hL ρ) (hD ρ hρ) (heta ρ hρ)
      (hfloor ρ hρ) (hcontract ρ hρ)
  rw [hhalf] at hre
  exact lt_irrefl _ hre

/-- **The four-budget form.**  The relative error is decomposed into the prime,
tail, mixed-interference and endpoint budgets; if their sum is `< 1` at every
zero, the Riemann Hypothesis follows.  This is the exact interface the remaining
analytic work has to meet. -/
theorem riemannHypothesis_of_relative_parts {c : ℝ} (hc : 0 < c)
    (L D ep et em ee : ℂ → ℝ)
    (hL : ∀ ρ : ℂ, 0 < L ρ)
    (hD : ∀ ρ : ℂ, completedRiemannZeta ρ = 0 → 0 ≤ D ρ)
    (hfloor : ∀ ρ : ℂ, completedRiemannZeta ρ = 0 →
      c * L ρ ^ 6 * zeroOffset ρ ^ 2 ≤ D ρ)
    (hsum : ∀ ρ : ℂ, completedRiemannZeta ρ = 0 →
      ep ρ + et ρ + em ρ + ee ρ < 1)
    (hcontract : ∀ ρ : ℂ, completedRiemannZeta ρ = 0 →
      D ρ ≤ (ep ρ + et ρ + em ρ + ee ρ) * D ρ) :
    RiemannHypothesis :=
  riemannHypothesis_of_relative_contraction hc L D
    (fun ρ => ep ρ + et ρ + em ρ + ee ρ) hL hD hfloor hsum hcontract

end RiemannAnalytic
