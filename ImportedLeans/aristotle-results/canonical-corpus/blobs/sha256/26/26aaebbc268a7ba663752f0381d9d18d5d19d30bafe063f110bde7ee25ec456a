/-
**G10 — the relative (contractive) endgame, and why an `o(L⁶)` budget is not
enough.**

Every budget proved so far in this programme has the *absolute* shape

    `D_ρ ≤ E(T)`,  `E(T) = o(L⁶)`,

while the geometric floor has the shape

    `c L⁶ α_ρ² ≤ D_ρ`.

Combining the two gives only `α_ρ = o(1)`: a *shrinking tube* around the
critical line, not the critical line.  This file proves that statement in both
directions, at literal strength:

* `tube_radius_of_absolute_budget` — the positive content of an absolute
  budget: `|α| ≤ √(E / (c L⁶))`;

* `absolute_budget_insufficient` — the negative content, stated as a theorem
  rather than a remark: for *any* strictly positive budget `E` there is a
  **nonzero** `α` compatible with the floor.  So no absolute budget, however
  small, can force `α = 0`.  A sequence of hypothetical zeros with
  `α_ρ = (log γ)^{-100}` really does survive the `o(L⁶)` architecture.

The replacement endgame is *relative*: the error must be bounded by a
contraction factor times the defect it is competing with,

    `E_ρ ≤ η(T) · D_ρ`,  `η(T) < 1`.

Then `D_ρ ≤ η D_ρ` with `D_ρ ≥ 0` forces `D_ρ = 0` exactly, and the floor
forces `α_ρ = 0` exactly — with **no detectability radius**.  This file proves
that endgame abstractly:

* `defect_eq_zero_of_relative_contraction`;
* `offLineTarget_excluded_of_relative_budget` — the exact-exclusion step;
* `totalRelativeError_lt_one_of_parts` and
  `totalRelativeError_eventually_contractive` — assembling four relative
  budgets (prime, tail, mixed interference, endpoint) into a single
  contraction factor that is eventually `< 1`;
* `offLineTarget_excluded_eventually` — the packaged form: given the floor, the
  relative error decomposition, and four vanishing relative budgets, every
  sufficiently high off-line target is excluded outright.

Nothing here is an analytic input: these are the *consumers*.  The theorem that
is still missing is the one that supplies `η_prime(T,H) → 0` for the literal
zeta source, and that remains this programme's first unproved theorem.
-/
import Mathlib

namespace RiemannAnalytic

open Filter Topology

/-! ## What an absolute budget does and does not give -/

/-- **The shrinking tube.**  A floor `c L⁶ α² ≤ D` together with an absolute
budget `D ≤ E` bounds the off-line displacement by `√(E/(cL⁶))` — and by
nothing better. -/
theorem tube_radius_of_absolute_budget {c L alpha D E : ℝ}
    (hc : 0 < c) (hL : 0 < L)
    (hfloor : c * L ^ 6 * alpha ^ 2 ≤ D) (hbudget : D ≤ E) :
    |alpha| ≤ Real.sqrt (E / (c * L ^ 6)) := by
  have hcL : 0 < c * L ^ 6 := by positivity
  have hsq : alpha ^ 2 ≤ E / (c * L ^ 6) := by
    rw [le_div_iff₀ hcL]
    nlinarith [hfloor, hbudget]
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq_eq_abs] at this

/-- **An absolute budget can never force `α = 0`.**  Whatever the constant `c`,
the scale `L` and the (strictly positive) budget `E`, there is a nonzero
displacement compatible with the floor.  This is the precise sense in which the
`o(L⁶)` architecture is insufficient for the Riemann Hypothesis. -/
theorem absolute_budget_insufficient {c L E : ℝ} (hc : 0 < c) (hL : 0 < L) (hE : 0 < E) :
    ∃ alpha : ℝ, alpha ≠ 0 ∧ c * L ^ 6 * alpha ^ 2 ≤ E := by
  have hcL : 0 < c * L ^ 6 := by positivity
  refine ⟨Real.sqrt (E / (c * L ^ 6)), ?_, ?_⟩
  · have : 0 < E / (c * L ^ 6) := div_pos hE hcL
    exact ne_of_gt (Real.sqrt_pos.mpr this)
  · rw [Real.sq_sqrt (le_of_lt (div_pos hE hcL)), mul_div_cancel₀ _ (ne_of_gt hcL)]

/-! ## The relative endgame -/

/-- **Contraction kills the defect.**  A nonnegative quantity dominated by a
strict contraction of itself is zero. -/
theorem defect_eq_zero_of_relative_contraction {D eta : ℝ}
    (hD : 0 ≤ D) (heta : eta < 1) (hcontract : D ≤ eta * D) : D = 0 := by
  by_contra hne
  have hpos : 0 < D := lt_of_le_of_ne hD (Ne.symm hne)
  nlinarith

/-- **Exact exclusion of an off-line target.**  With the geometric floor
`c L⁶ α² ≤ D` and a *relative* budget `D ≤ η D`, `η < 1`, the displacement is
exactly zero.  There is no detectability radius: the conclusion is `α = 0`, not
`|α|` small. -/
theorem offLineTarget_excluded_of_relative_budget {c L alpha D eta : ℝ}
    (hc : 0 < c) (hL : 0 < L) (hD : 0 ≤ D) (heta : eta < 1)
    (hfloor : c * L ^ 6 * alpha ^ 2 ≤ D) (hcontract : D ≤ eta * D) :
    alpha = 0 := by
  have hzero : D = 0 := defect_eq_zero_of_relative_contraction hD heta hcontract
  have hcL : 0 < c * L ^ 6 := by positivity
  have : alpha ^ 2 ≤ 0 := by
    rw [hzero] at hfloor
    nlinarith
  have : alpha ^ 2 = 0 := le_antisymm this (sq_nonneg alpha)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this

/-- Assembling four relative budgets into one contraction factor. -/
theorem totalRelativeError_lt_one_of_parts {ep et em ee : ℝ}
    (hp : ep < 1 / 4) (ht : et < 1 / 4) (hm : em < 1 / 4) (he : ee < 1 / 4) :
    ep + et + em + ee < 1 := by linarith

/-- **`totalRelativeErrorEventuallyContractive`.**  If each of the four relative
budgets (prime, source tail, mixed interference, endpoint) tends to `0` as the
height grows, then their sum is eventually a strict contraction factor. -/
theorem totalRelativeError_eventually_contractive
    (ep et em ee : ℝ → ℝ)
    (hp : Tendsto ep atTop (𝓝 0)) (ht : Tendsto et atTop (𝓝 0))
    (hm : Tendsto em atTop (𝓝 0)) (he : Tendsto ee atTop (𝓝 0)) :
    ∀ᶠ T in atTop, ep T + et T + em T + ee T < 1 := by
  have hsum : Tendsto (fun T => ep T + et T + em T + ee T) atTop (𝓝 0) := by
    simpa using ((hp.add ht).add hm).add he
  have := hsum.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  simpa using this

/-- **The packaged endgame.**  Suppose that at every height `T` there is a
defect `D T ≥ 0` obeying the geometric floor for the displacement `alpha T`,
that the total error is decomposed into four relative budgets, and that each of
those budgets vanishes as `T → ∞`.  Then every sufficiently high off-line
target is excluded exactly. -/
theorem offLineTarget_excluded_eventually
    {c : ℝ} (hc : 0 < c) (L alpha D ep et em ee : ℝ → ℝ)
    (hL : ∀ T, 0 < L T) (hD : ∀ T, 0 ≤ D T)
    (hfloor : ∀ T, c * (L T) ^ 6 * (alpha T) ^ 2 ≤ D T)
    (hcontract : ∀ T, D T ≤ (ep T + et T + em T + ee T) * D T)
    (hp : Tendsto ep atTop (𝓝 0)) (ht : Tendsto et atTop (𝓝 0))
    (hm : Tendsto em atTop (𝓝 0)) (he : Tendsto ee atTop (𝓝 0)) :
    ∀ᶠ T in atTop, alpha T = 0 := by
  filter_upwards [totalRelativeError_eventually_contractive ep et em ee hp ht hm he] with T hT
  exact offLineTarget_excluded_of_relative_budget hc (hL T) (hD T) hT
    (hfloor T) (hcontract T)

/-! ## What the missing prime theorem has to look like

The budgets proved for the anchored prime observable so far have the shape
`P ≤ C·δ²·L⁶` (a localisation gain in the log-block length), with **no factor
`α²`**.  The next two lemmas isolate exactly what changes if the missing
analytic input keeps that factor: an `α²`-carrying prime bound converts, with
no further work, into a *relative* budget of the kind the endgame consumes, and
then a small enough localisation parameter excludes the off-line target
outright. -/

/-- An `α²`-carrying prime bound is automatically a relative budget against the
geometric floor: `P ≤ Cδ²α²L⁶` and `cL⁶α² ≤ D` give `P ≤ (Cδ²/c)·D`. -/
theorem relative_budget_of_alpha_factor {C c delta alpha L P D : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C)
    (hP : P ≤ C * delta ^ 2 * alpha ^ 2 * L ^ 6)
    (hfloor : c * L ^ 6 * alpha ^ 2 ≤ D) :
    P ≤ C * delta ^ 2 / c * D := by
  have hfac : 0 ≤ C * delta ^ 2 / c := by positivity
  have hstep : C * delta ^ 2 / c * (c * L ^ 6 * alpha ^ 2)
      ≤ C * delta ^ 2 / c * D := by
    exact mul_le_mul_of_nonneg_left hfloor hfac
  have heq : C * delta ^ 2 / c * (c * L ^ 6 * alpha ^ 2)
      = C * delta ^ 2 * alpha ^ 2 * L ^ 6 := by
    field_simp
  linarith [hP, hstep, heq.symm.le, heq.le]

/-- **The shape of the decisive step.**  If the anchored defect is dominated by
an `α²`-carrying prime bound with localisation parameter `δ` small enough that
`Cδ² < c`, then the off-line displacement is exactly zero. -/
theorem offLineTarget_excluded_of_alpha_factor_budget
    {C c delta alpha L D : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (hL : 0 < L) (hD : 0 ≤ D)
    (hsmall : C * delta ^ 2 < c)
    (hfloor : c * L ^ 6 * alpha ^ 2 ≤ D)
    (hprime : D ≤ C * delta ^ 2 * alpha ^ 2 * L ^ 6) :
    alpha = 0 := by
  have hrel : D ≤ C * delta ^ 2 / c * D :=
    relative_budget_of_alpha_factor hc hC hprime hfloor
  have heta : C * delta ^ 2 / c < 1 := (div_lt_one hc).mpr hsmall
  exact offLineTarget_excluded_of_relative_budget hc hL hD heta hfloor hrel

/-- The same conclusion phrased as the contrapositive that the programme
actually consumes: a *positive* defect is incompatible with a contractive
relative budget. -/
theorem no_positive_defect_of_relative_budget {D eta : ℝ}
    (hD : 0 < D) (heta : eta < 1) (hcontract : D ≤ eta * D) : False := by
  have := defect_eq_zero_of_relative_contraction (le_of_lt hD) heta hcontract
  exact absurd this (ne_of_gt hD)

end RiemannAnalytic
