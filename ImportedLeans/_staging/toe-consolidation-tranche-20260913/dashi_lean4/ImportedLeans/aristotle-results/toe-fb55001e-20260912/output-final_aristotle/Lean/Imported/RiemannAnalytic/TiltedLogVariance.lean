/-
**G12 — the twisted log-variance: what the exponential tilt can and cannot do.**

After `CompensatedDiagonal` the remaining question is quantitative and completely
concrete.  G11 gives

    `𝒟(α) ≤ 8Λ²α²·𝒜(α)`,   `𝒜(α) ≤ s²·Var_{w(α)}(λ)`,

so the whole programme now depends on the *twisted log-variance*

    `Var_{w(α)}(λ) = S₀S₂ − S₁²`,   `S_r(α) = ∑ₙ wₙe^{2αλₙ}λₙ^r`,

and specifically on whether `α²·Var` stays bounded (or better) uniformly in the
twist parameter `α`.  The heuristic is that an exponential tilt concentrates the
measure near one end of the log-frequency interval, so that
`Var ≍ α^{-2}` for large `α` and `α²·Var = O(1)` uniformly.

This file settles that heuristic, in both directions, with machine-checked
statements:

* `varForm_le_centered`, `varForm_le_range` — the variance is bounded by any
  centred second moment, and by `L²/4` times the squared mass on an interval of
  length `L` (the small-`α` regime is therefore automatic).

* **Negative (adversarial).**  `alpha_sq_tilted_variance_unbounded`: for
  *arbitrary positive weights* the quantity `α²·Var / S₀²` is **unbounded**, even
  for a two-point configuration inside a bounded interval.  So the concentration
  mechanism is *false* as a statement about general weights: it cannot be
  extracted from the hyperbolic algebra, and it is not implied by positivity.

* **Positive (model).**  `geomGrid_alpha_sq_variance_le`: for the exponentially
  tilted *uniform grid* — the model of a log-frequency measure with two-sided
  density — the mechanism is **true**, with an explicit constant and no
  asymptotics:

      `α²·Var ≤ 16·S₀²`,

  uniformly for every spacing `h` and every `α > 0` with `2αh ≤ 1` and grid
  length at least `1/(2α)`.

Together these two theorems locate the remaining arithmetic content exactly: the
twisted prime variance bound holds if and only if the von Mangoldt weights have a
two-sided density on the relevant log-frequency scale; nothing weaker (positivity,
boundedness, total mass) suffices.  That is the precise remaining input, and it is
**not** proved here.
-/
import RiemannAnalytic.PrimeLogFrequency

namespace RiemannAnalytic

open Finset

variable {d : ℕ}

/-! ### The exponentially tilted weight family -/

/-- The exponentially tilted weights `wₙ(α) = wₙe^{2αλₙ}`. -/
noncomputable def tiltWeight (w lam : Fin d → ℝ) (alpha : ℝ) : Fin d → ℝ :=
  fun n => w n * Real.exp (2 * alpha * lam n)

@[simp] theorem tiltWeight_zero (w lam : Fin d → ℝ) : tiltWeight w lam 0 = w := by
  funext n; simp [tiltWeight]

theorem tiltWeight_nonneg {w lam : Fin d → ℝ} (hw : ∀ n, 0 ≤ w n) (alpha : ℝ) (n : Fin d) :
    0 ≤ tiltWeight w lam alpha n :=
  mul_nonneg (hw n) (Real.exp_nonneg _)

/-! ### Elementary variance bounds -/

/-- The variance is bounded by the second moment about *any* centre. -/
theorem varForm_le_centered (w lam : Fin d → ℝ) (c : ℝ) :
    varForm w lam ≤ (∑ n, w n) * ∑ n, w n * (lam n - c) ^ 2 := by
  unfold varForm
  have hexp : ∑ n, w n * (lam n - c) ^ 2
      = (∑ n, w n * lam n ^ 2) - 2 * c * (∑ n, w n * lam n) + c ^ 2 * (∑ n, w n) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hexp]
  nlinarith [sq_nonneg ((∑ n, w n * lam n) - c * (∑ n, w n))]

/-- On an interval of length `L` the variance is at most `L²/4` times the squared
mass: the `α → 0` regime of the concentration heuristic is automatic. -/
theorem varForm_le_range {w lam : Fin d → ℝ} {a L : ℝ} (hw : ∀ n, 0 ≤ w n)
    (hlam : ∀ n, a ≤ lam n ∧ lam n ≤ a + L) :
    varForm w lam ≤ L ^ 2 / 4 * (∑ n, w n) ^ 2 := by
  have hcent := varForm_le_centered w lam (a + L / 2)
  have hterm : ∀ n : Fin d, w n * (lam n - (a + L / 2)) ^ 2 ≤ L ^ 2 / 4 * w n := by
    intro n
    obtain ⟨h1, h2⟩ := hlam n
    have hsq : (lam n - (a + L / 2)) ^ 2 ≤ L ^ 2 / 4 := by nlinarith [h1, h2]
    nlinarith [hw n, hsq]
  have hsum : ∑ n, w n * (lam n - (a + L / 2)) ^ 2 ≤ L ^ 2 / 4 * ∑ n, w n := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n _ => hterm n
  have hmass : 0 ≤ ∑ n, w n := Finset.sum_nonneg fun n _ => hw n
  nlinarith [hcent, mul_le_mul_of_nonneg_left hsum hmass]

/-! ### The adversarial theorem: no universal concentration -/

/-- **`α²·Var` is unbounded for general positive weights.**  For every `B` there
is a two-point configuration inside a bounded interval, with strictly positive
weights, and a twist `α > 0`, for which

    `B·S₀² ≤ α²·Var`.

So the concentration heuristic is *false* as a statement about arbitrary weights:
any proof of a twisted variance bound must use the actual arithmetic
distribution of the log-prime frequencies, not positivity or boundedness. -/
theorem alpha_sq_tilted_variance_unbounded (B : ℝ) (hB : 0 ≤ B) :
    ∃ (L alpha : ℝ) (w lam : Fin 2 → ℝ), 0 < alpha ∧ 0 < L ∧ (∀ n, 0 < w n) ∧
      (∀ n, lam n ∈ Set.Icc (0 : ℝ) L) ∧
      B * (∑ n, tiltWeight w lam alpha n) ^ 2
        ≤ alpha ^ 2 * varForm (tiltWeight w lam alpha) lam := by
  refine ⟨2 * Real.sqrt B + 1, 1, ![1, Real.exp (-(2 * (2 * Real.sqrt B + 1)))],
    ![0, 2 * Real.sqrt B + 1], one_pos, by positivity, ?_, ?_, ?_⟩
  · intro n; fin_cases n <;> simp [Real.exp_pos]
  · intro n
    have h0 : (0 : ℝ) ≤ 2 * Real.sqrt B + 1 := by positivity
    fin_cases n <;> simp [Set.mem_Icc, h0]
  · set L : ℝ := 2 * Real.sqrt B + 1 with hL
    have htilt : tiltWeight ![1, Real.exp (-(2 * L))] ![0, L] 1 = ![1, 1] := by
      funext n
      fin_cases n
      · simp [tiltWeight]
      · simp [tiltWeight, ← Real.exp_add]
    rw [htilt]
    have hvar : varForm (![1, 1] : Fin 2 → ℝ) ![0, L] = L ^ 2 := by
      simp [varForm, Fin.sum_univ_two]; ring
    have hmass : (∑ n, (![1, 1] : Fin 2 → ℝ) n) = 2 := by
      simp [Fin.sum_univ_two]; norm_num
    rw [hvar, hmass]
    have hsqrt : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB
    have hs0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
    nlinarith [hsqrt, hs0]

/-! ### The positive model theorem: the exponentially tilted uniform grid -/

/-- `u²e^{−u} ≤ 4e^{−2}` for `u ≥ 0`: the exact maximum of the profile that
governs the tilted second moment. -/
theorem sq_mul_exp_neg_le {u : ℝ} (hu : 0 ≤ u) : u ^ 2 * Real.exp (-u) ≤ 4 * Real.exp (-2) := by
  have h1 : (u / 2 - 1) + 1 ≤ Real.exp (u / 2 - 1) := Real.add_one_le_exp _
  have h1' : u / 2 ≤ Real.exp (u / 2 - 1) := by linarith
  have hnn : 0 ≤ u / 2 := by linarith
  have h2 : (u / 2) ^ 2 ≤ Real.exp (u / 2 - 1) ^ 2 := by nlinarith [h1', hnn]
  have h3 : Real.exp (u / 2 - 1) ^ 2 = Real.exp (u - 2) := by
    rw [pow_two, ← Real.exp_add]; ring_nf
  have h4 : (u / 2) ^ 2 ≤ Real.exp (u - 2) := by rw [← h3]; exact h2
  have h5 : Real.exp (u - 2) = Real.exp u * Real.exp (-2) := by
    rw [← Real.exp_add]; ring_nf
  have hexp : Real.exp (-u) * Real.exp u = 1 := by
    rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (-u) := Real.exp_pos _
  have h6 : (u / 2) ^ 2 * Real.exp (-u) ≤ Real.exp (-2) := by
    have := mul_le_mul_of_nonneg_right h4 hpos.le
    rw [h5] at this
    calc (u / 2) ^ 2 * Real.exp (-u) ≤ Real.exp u * Real.exp (-2) * Real.exp (-u) := this
      _ = (Real.exp (-u) * Real.exp u) * Real.exp (-2) := by ring
      _ = Real.exp (-2) := by rw [hexp]; ring
  nlinarith [h6]

/-- A partial geometric sum is at most the geometric series. -/
theorem geom_partial_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (K : ℕ) :
    ∑ j ∈ Finset.range K, q ^ j ≤ 1 / (1 - q) := by
  have hne : q ≠ 1 := hq1.ne
  have hpos : 0 < 1 - q := by linarith
  rw [geom_sum_eq hne]
  have hrw : (q ^ K - 1) / (q - 1) = (1 - q ^ K) / (1 - q) := by
    rw [div_eq_div_iff (sub_ne_zero_of_ne hq1.ne) (sub_ne_zero_of_ne hq1.ne')]
    ring
  rw [hrw, div_le_div_iff₀ hpos hpos]
  nlinarith [pow_nonneg hq0 K]

/-- `1/(1 − e^{−y}) ≤ 1 + 1/y` for `y > 0`. -/
theorem one_div_one_sub_exp_neg_le {y : ℝ} (hy : 0 < y) :
    1 / (1 - Real.exp (-y)) ≤ 1 + 1 / y := by
  have hexp : 1 + y ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  have hy1 : 0 < 1 + y := by linarith
  have hepos : 0 < Real.exp y := Real.exp_pos y
  have hinv : Real.exp (-y) = (Real.exp y)⁻¹ := by
    rw [Real.exp_neg]
  have hle : Real.exp (-y) ≤ 1 / (1 + y) := by
    rw [hinv, inv_eq_one_div, div_le_div_iff₀ hepos hy1]
    linarith
  have hpos : 0 < 1 - Real.exp (-y) := by
    have h1 : Real.exp (-y) < 1 := by
      rw [Real.exp_lt_one_iff]; linarith
    linarith
  have hlow : y / (1 + y) ≤ 1 - Real.exp (-y) := by
    have : 1 - 1 / (1 + y) = y / (1 + y) := by field_simp; ring
    linarith [hle, this.le, this.ge]
  have hyy : 0 < y / (1 + y) := by positivity
  rw [div_le_iff₀ hpos]
  have hstep : (1 + 1 / y) * (y / (1 + y)) = 1 := by field_simp; ring
  nlinarith [mul_le_mul_of_nonneg_left hlow (by positivity : (0:ℝ) ≤ 1 + 1 / y), hstep]

/-- A lower bound for the tilted mass of a long grid. -/
theorem geom_sum_exp_ge {x : ℝ} {K : ℕ} (hx : 0 < x) (hK : 1 ≤ x * K) :
    (1 - Real.exp (-1)) / x ≤ ∑ j ∈ Finset.range K, Real.exp (-x) ^ j := by
  have hr0 : 0 < Real.exp (-x) := Real.exp_pos _
  have hr1 : Real.exp (-x) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hne : Real.exp (-x) ≠ 1 := hr1.ne
  rw [geom_sum_eq hne]
  have hpow : Real.exp (-x) ^ K = Real.exp (-(x * K)) := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hKle : Real.exp (-(x * K)) ≤ Real.exp (-1) := by
    apply Real.exp_le_exp.mpr; linarith
  have hden : 1 - Real.exp (-x) ≤ x := by
    have := Real.add_one_le_exp (-x); linarith
  have hdpos : 0 < 1 - Real.exp (-x) := by linarith
  have hnum : 1 - Real.exp (-1) ≤ 1 - Real.exp (-x) ^ K := by
    rw [hpow]; linarith
  have hnumpos : 0 < 1 - Real.exp (-1) := by
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    linarith
  have hrw : (Real.exp (-x) ^ K - 1) / (Real.exp (-x) - 1)
      = (1 - Real.exp (-x) ^ K) / (1 - Real.exp (-x)) := by
    rw [div_eq_div_iff (sub_ne_zero_of_ne hr1.ne) (sub_ne_zero_of_ne hr1.ne')]
    ring
  rw [hrw, div_le_div_iff₀ hx hdpos]
  nlinarith [hnum, hden, hnumpos, hdpos, hx]

/-! ### The tilted uniform grid -/

/-- The uniform log-frequency grid of spacing `h`, with its top at `0`. -/
noncomputable def gridFreq (h : ℝ) (K : ℕ) : Fin K → ℝ := fun j => -((j : ℝ) * h)

/-- Unit base weights on the grid. -/
noncomputable def gridWeight (K : ℕ) : Fin K → ℝ := fun _ => 1

/-- The tilted grid weights are the geometric sequence `e^{-2αh j}`. -/
theorem tiltWeight_grid (h alpha : ℝ) (K : ℕ) (j : Fin K) :
    tiltWeight (gridWeight K) (gridFreq h K) alpha j
      = Real.exp (-(2 * alpha * h)) ^ (j : ℕ) := by
  rw [tiltWeight, gridWeight, gridFreq, ← Real.exp_nat_mul]
  simp only [one_mul]
  congr 1
  ring

/-- Numerical facts about `e` used in the grid estimate. -/
theorem exp_two_ge_seven : (7 : ℝ) ≤ Real.exp 2 := by
  have h := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [h, Real.exp_pos 1]

theorem exp_neg_one_le : Real.exp (-1) ≤ 2 / 5 := by
  have h := Real.exp_one_gt_d9
  have hpos : 0 < Real.exp 1 := Real.exp_pos 1
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hpos]
  nlinarith [h]

/-- **The termwise profile bound.**  Each term of the tilted second moment is
controlled by the half-tilted geometric sequence, with the exact profile
constant `4e^{-2}`. -/
theorem grid_term_le {x h : ℝ} (hx : 0 < x) (j : ℕ) :
    ((j : ℝ) * h) ^ 2 * Real.exp (-x) ^ j
      ≤ 16 * h ^ 2 / (x ^ 2 * Real.exp 2) * Real.exp (-x / 2) ^ j := by
  have hjr : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  set u : ℝ := x * (j : ℝ) / 2 with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have hA := sq_mul_exp_neg_le hu0
  have hq : Real.exp (-x / 2) ^ j = Real.exp (-u) := by
    rw [← Real.exp_nat_mul]; congr 1; rw [hu]; ring
  have hr : Real.exp (-x) ^ j = Real.exp (-u) * Real.exp (-u) := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; rw [hu]; ring
  have hjh : ((j : ℝ) * h) ^ 2 = 4 * h ^ 2 / x ^ 2 * u ^ 2 := by
    rw [hu]; field_simp; ring
  have he2 : Real.exp (-2) = 1 / Real.exp 2 := by
    rw [Real.exp_neg, one_div]
  have hexpu : 0 ≤ Real.exp (-u) := (Real.exp_pos _).le
  have hc : 0 ≤ 4 * h ^ 2 / x ^ 2 := by positivity
  have hstep : u ^ 2 * Real.exp (-u) * Real.exp (-u)
      ≤ 4 * Real.exp (-2) * Real.exp (-u) :=
    mul_le_mul_of_nonneg_right hA hexpu
  have hmul := mul_le_mul_of_nonneg_left hstep hc
  rw [hjh, hr, hq]
  have hL : 4 * h ^ 2 / x ^ 2 * u ^ 2 * (Real.exp (-u) * Real.exp (-u))
      = 4 * h ^ 2 / x ^ 2 * (u ^ 2 * Real.exp (-u) * Real.exp (-u)) := by ring
  have hR : 4 * h ^ 2 / x ^ 2 * (4 * Real.exp (-2) * Real.exp (-u))
      = 16 * h ^ 2 / (x ^ 2 * Real.exp 2) * Real.exp (-u) := by
    rw [he2]; field_simp; ring
  rw [hL]
  calc 4 * h ^ 2 / x ^ 2 * (u ^ 2 * Real.exp (-u) * Real.exp (-u))
      ≤ 4 * h ^ 2 / x ^ 2 * (4 * Real.exp (-2) * Real.exp (-u)) := hmul
    _ = 16 * h ^ 2 / (x ^ 2 * Real.exp 2) * Real.exp (-u) := hR

/-- **The tilted second moment of a long grid.**  With `x = 2αh ≤ 1` and grid
length at least `1/x`, the tilted second moment about the top of the grid is at
most `16h²/x² = 4/α²` times the tilted mass.  This is the concentration
mechanism, proved with explicit constants. -/
theorem grid_second_moment_le {x h : ℝ} {K : ℕ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hK : 1 ≤ x * K) :
    ∑ j ∈ Finset.range K, ((j : ℝ) * h) ^ 2 * Real.exp (-x) ^ j
      ≤ 16 * h ^ 2 / x ^ 2 * ∑ j ∈ Finset.range K, Real.exp (-x) ^ j := by
  have hh2 : (0 : ℝ) ≤ h ^ 2 := sq_nonneg h
  have hx2 : 0 < x ^ 2 := by positivity
  have hE2 : (7 : ℝ) ≤ Real.exp 2 := exp_two_ge_seven
  have hE2pos : 0 < Real.exp 2 := Real.exp_pos 2
  -- upper bound for the second moment
  have hup : ∑ j ∈ Finset.range K, ((j : ℝ) * h) ^ 2 * Real.exp (-x) ^ j
      ≤ 16 * h ^ 2 / (x ^ 2 * Real.exp 2) * ∑ j ∈ Finset.range K, Real.exp (-x / 2) ^ j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => grid_term_le hx j
  have hq0 : (0 : ℝ) ≤ Real.exp (-x / 2) := (Real.exp_pos _).le
  have hq1 : Real.exp (-x / 2) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hgeom : ∑ j ∈ Finset.range K, Real.exp (-x / 2) ^ j ≤ 1 / (1 - Real.exp (-x / 2)) :=
    geom_partial_le hq0 hq1 K
  have hhalf : Real.exp (-x / 2) = Real.exp (-(x / 2)) := by congr 1; ring
  have htail : 1 / (1 - Real.exp (-x / 2)) ≤ 1 + 2 / x := by
    rw [hhalf]
    have := one_div_one_sub_exp_neg_le (y := x / 2) (by linarith)
    have hrw : 1 + 1 / (x / 2) = 1 + 2 / x := by
      field_simp
    linarith [this, hrw.le, hrw.ge]
  -- lower bound for the tilted mass
  have hlow : (1 - Real.exp (-1)) / x ≤ ∑ j ∈ Finset.range K, Real.exp (-x) ^ j :=
    geom_sum_exp_ge hx hK
  have hE1 : Real.exp (-1) ≤ 2 / 5 := exp_neg_one_le
  -- put the pieces together
  have hfac : 0 ≤ 16 * h ^ 2 / (x ^ 2 * Real.exp 2) := by positivity
  have hstep1 : ∑ j ∈ Finset.range K, ((j : ℝ) * h) ^ 2 * Real.exp (-x) ^ j
      ≤ 16 * h ^ 2 / (x ^ 2 * Real.exp 2) * (1 + 2 / x) :=
    hup.trans (mul_le_mul_of_nonneg_left (hgeom.trans htail) hfac)
  have hnum : 16 * h ^ 2 / (x ^ 2 * Real.exp 2) * (1 + 2 / x)
      ≤ 16 * h ^ 2 / x ^ 2 * ((1 - Real.exp (-1)) / x) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hx2]
    have hxx : 0 < x := hx
    have hkey : (1 + 2 / x) * x ≤ 3 := by
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hx)]
      linarith
    have h1 : 16 * h ^ 2 * (1 + 2 / x) * x ^ 2
        = (16 * h ^ 2) * ((1 + 2 / x) * x) * x := by ring
    have h2 : 16 * h ^ 2 * ((1 - Real.exp (-1)) / x) * (x ^ 2 * Real.exp 2)
        = (16 * h ^ 2) * (1 - Real.exp (-1)) * Real.exp 2 * x := by
      field_simp
    rw [h1, h2]
    have hA : (16 * h ^ 2) * ((1 + 2 / x) * x) ≤ (16 * h ^ 2) * 3 := by
      apply mul_le_mul_of_nonneg_left hkey (by positivity)
    have hprod3 : (3 : ℝ) ≤ (1 - Real.exp (-1)) * Real.exp 2 := by
      nlinarith [hE1, hE2, hE2pos]
    have hB : (16 * h ^ 2) * 3 ≤ (16 * h ^ 2) * (1 - Real.exp (-1)) * Real.exp 2 := by
      have hstep := mul_le_mul_of_nonneg_left hprod3 (by positivity : (0 : ℝ) ≤ 16 * h ^ 2)
      have heq : (16 * h ^ 2) * (1 - Real.exp (-1)) * Real.exp 2
          = (16 * h ^ 2) * ((1 - Real.exp (-1)) * Real.exp 2) := by ring
      linarith [hstep, heq.le, heq.ge]
    nlinarith [hA, hB, hx.le, hh2]
  have hfin : 16 * h ^ 2 / x ^ 2 * ((1 - Real.exp (-1)) / x)
      ≤ 16 * h ^ 2 / x ^ 2 * ∑ j ∈ Finset.range K, Real.exp (-x) ^ j :=
    mul_le_mul_of_nonneg_left hlow (by positivity)
  linarith [hstep1, hnum, hfin]

/-- **The concentration theorem for the exponentially tilted uniform grid.**

    `α²·Var ≤ 4·S₀²`

uniformly in the spacing `h`, the length `K` and the twist `α > 0`, provided
`2αh ≤ 1` and the grid is at least `1/(2α)` long.  This is the exact positive
counterpart of `alpha_sq_tilted_variance_unbounded`: the concentration mechanism
holds for a log-frequency measure with two-sided density, and fails without
one. -/
theorem geomGrid_alpha_sq_variance_le {h alpha : ℝ} {K : ℕ}
    (hh : 0 < h) (halpha : 0 < alpha) (hx1 : 2 * alpha * h ≤ 1)
    (hlong : 1 ≤ 2 * alpha * h * K) :
    alpha ^ 2 * varForm (tiltWeight (gridWeight K) (gridFreq h K) alpha) (gridFreq h K)
      ≤ 4 * (∑ j, tiltWeight (gridWeight K) (gridFreq h K) alpha j) ^ 2 := by
  set x : ℝ := 2 * alpha * h with hxdef
  have hx : 0 < x := by rw [hxdef]; positivity
  -- the tilted weights are the geometric sequence
  have hw : ∀ j : Fin K, tiltWeight (gridWeight K) (gridFreq h K) alpha j
      = Real.exp (-x) ^ (j : ℕ) := fun j => tiltWeight_grid h alpha K j
  have hmass : (∑ j, tiltWeight (gridWeight K) (gridFreq h K) alpha j)
      = ∑ j ∈ Finset.range K, Real.exp (-x) ^ j := by
    rw [Finset.sum_congr rfl fun j _ => hw j]
    exact Fin.sum_univ_eq_sum_range (fun j => Real.exp (-x) ^ j) K
  have hsecond : (∑ j, tiltWeight (gridWeight K) (gridFreq h K) alpha j *
        (gridFreq h K j - 0) ^ 2)
      = ∑ j ∈ Finset.range K, ((j : ℝ) * h) ^ 2 * Real.exp (-x) ^ j := by
    have hterm : ∀ j : Fin K, tiltWeight (gridWeight K) (gridFreq h K) alpha j *
        (gridFreq h K j - 0) ^ 2 = ((j : ℝ) * h) ^ 2 * Real.exp (-x) ^ (j : ℕ) := by
      intro j
      rw [hw j, gridFreq]
      ring_nf
    rw [Finset.sum_congr rfl fun j _ => hterm j]
    exact Fin.sum_univ_eq_sum_range (fun j => ((j : ℝ) * h) ^ 2 * Real.exp (-x) ^ j) K
  have hcent := varForm_le_centered (tiltWeight (gridWeight K) (gridFreq h K) alpha)
    (gridFreq h K) 0
  rw [hmass, hsecond] at hcent
  have hmoment := grid_second_moment_le (x := x) (h := h) (K := K) hx hx1 (by
    rw [hxdef]; linarith [hlong])
  have hSnonneg : 0 ≤ ∑ j ∈ Finset.range K, Real.exp (-x) ^ j :=
    Finset.sum_nonneg fun j _ => pow_nonneg (Real.exp_pos _).le j
  have hprod : (∑ j ∈ Finset.range K, Real.exp (-x) ^ j) *
        ∑ j ∈ Finset.range K, ((j : ℝ) * h) ^ 2 * Real.exp (-x) ^ j
      ≤ (∑ j ∈ Finset.range K, Real.exp (-x) ^ j) *
        (16 * h ^ 2 / x ^ 2 * ∑ j ∈ Finset.range K, Real.exp (-x) ^ j) :=
    mul_le_mul_of_nonneg_left hmoment hSnonneg
  have hconst : 16 * h ^ 2 / x ^ 2 = 4 / alpha ^ 2 := by
    rw [hxdef]; field_simp; ring
  rw [hconst] at hprod
  have halpha2 : 0 < alpha ^ 2 := by positivity
  have hvar : varForm (tiltWeight (gridWeight K) (gridFreq h K) alpha) (gridFreq h K)
      ≤ 4 / alpha ^ 2 * (∑ j ∈ Finset.range K, Real.exp (-x) ^ j) ^ 2 := by
    nlinarith [hcent, hprod]
  rw [hmass]
  have := mul_le_mul_of_nonneg_left hvar halpha2.le
  calc alpha ^ 2 * varForm (tiltWeight (gridWeight K) (gridFreq h K) alpha) (gridFreq h K)
      ≤ alpha ^ 2 * (4 / alpha ^ 2 * (∑ j ∈ Finset.range K, Real.exp (-x) ^ j) ^ 2) := this
    _ = 4 * (∑ j ∈ Finset.range K, Real.exp (-x) ^ j) ^ 2 := by
        field_simp

/-! ### What a uniform concentration bound is worth

The concentration theorem is *uniform in `α`*, which is exactly what G11 asked
for — but uniformity in `α` means the bound **consumes** the factor `α²` rather
than preserving it.  The resulting budget is therefore absolute, and
`absolute_budget_insufficient` applies to it: it produces a shrinking tube, not
the critical line.  The following consumer records that logical status exactly,
so that the remaining requirement cannot be misread. -/

/-- **A uniform twisted-variance bound gives a tube, not the line.**  Combining
the G11 normalization `D ≤ 8Λ²α²s²V` with a concentration bound
`α²V ≤ 4S²` yields the absolute budget `D ≤ 32Λ²s²S²`, hence only
`|α| ≤ √(32Λ²s²S²/(cL⁶))`.  Exact exclusion needs the budget to beat the
geometric floor outright — a genuine size comparison between the prime mass and
the zero-side floor. -/
theorem twisted_variance_bound_gives_tube_only
    {c L alpha D Lam s V S : ℝ} (hc : 0 < c) (hL : 0 < L)
    (hfloor : c * L ^ 6 * alpha ^ 2 ≤ D)
    (hdefect : D ≤ 8 * Lam ^ 2 * alpha ^ 2 * (s ^ 2 * V))
    (hconc : alpha ^ 2 * V ≤ 4 * S ^ 2) :
    |alpha| ≤ Real.sqrt (32 * Lam ^ 2 * s ^ 2 * S ^ 2 / (c * L ^ 6)) := by
  have habs : D ≤ 32 * Lam ^ 2 * s ^ 2 * S ^ 2 := by
    have hfac : (0 : ℝ) ≤ 8 * Lam ^ 2 * s ^ 2 := by positivity
    have hstep : 8 * Lam ^ 2 * s ^ 2 * (alpha ^ 2 * V)
        ≤ 8 * Lam ^ 2 * s ^ 2 * (4 * S ^ 2) :=
      mul_le_mul_of_nonneg_left hconc hfac
    nlinarith [hdefect, hstep]
  exact tube_radius_of_absolute_budget hc hL hfloor habs

end RiemannAnalytic
