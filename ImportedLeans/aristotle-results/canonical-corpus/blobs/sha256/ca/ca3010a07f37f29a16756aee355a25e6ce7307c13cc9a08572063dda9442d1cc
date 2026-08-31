/-
# Row A — the shooting coordinate `u = g⁻²`, and the weights it manufactures

The Row-A shooting map is phrased in the inverse squared coupling `u = g⁻²`, and
the point of that coordinate is that it *manufactures smallness*: since
`g(u) = u^{-1/2}` has `dg/du = −½g³`, a channel sensitivity of order `g³` in the
coupling becomes a sensitivity of order `g⁶` in the shooting coordinate.

This file proves the three purely quantitative facts that turn the differentiated
channel majorants of `LiteralChannelSensitivity` into a *summable* per-shell
sensitivity:

* `abs_couplingOf_sub_le` — `|g(u) − g(v)| ≤ ½·u₀^{-3/2}·|u − v|` for
  `u, v ≥ u₀ > 0`, i.e. the exact `−½g³` law in Lipschitz form, with no
  differentiability side conditions;
* `couplingOf_le` — the tube bound `g(u) ≤ g(u₀) = u₀^{-1/2}`;
* `sum_inv_cube_linear_le` — the **weighted** summation
  `Σ_{j<K}(u₀+bj)^{-3} ≤ u₀^{-3} + 1/(2b u₀²)`, proved by an exact telescoping
  comparison, so the trajectory weights `g_j⁶` are *retained* rather than
  replaced by their supremum.  This is the estimate that makes the cumulative
  sensitivity `O(1/(b u₀²))`, hence `< 1` for a sufficiently small bare coupling.
-/
import RequestProject.YangMills.RunningCouplingWindow

namespace YangMills

open Finset

/-! ## 1. The coupling as a function of the shooting coordinate -/

/-- The coupling read off from the inverse squared coupling: `g(u) = u^{-1/2}`. -/
noncomputable def couplingOf (u : ℝ) : ℝ := Real.sqrt u⁻¹

theorem couplingOf_nonneg (u : ℝ) : 0 ≤ couplingOf u := Real.sqrt_nonneg _

/-- The shooting coordinate really is the inverse squared coupling. -/
theorem couplingOf_sq {u : ℝ} (hu : 0 ≤ u) : couplingOf u ^ 2 = u⁻¹ := by
  rw [couplingOf, Real.sq_sqrt (inv_nonneg.mpr hu)]

/-- On the tube `u ≥ u₀` the coupling is bounded by its value at the floor. -/
theorem couplingOf_le {u₀ u : ℝ} (hu₀ : 0 < u₀) (hu : u₀ ≤ u) :
    couplingOf u ≤ couplingOf u₀ :=
  Real.sqrt_le_sqrt (inv_anti₀ hu₀ hu)

/-- **The `dg/du = −½g³` law, in Lipschitz form.**  On the tube `u, v ≥ u₀ > 0`,
`|g(u) − g(v)| ≤ ½·g(u₀)³·|u − v| = ½·u₀^{-3/2}·|u − v|`.  No differentiability
is invoked: with `a = √u`, `b = √v` the identity `a⁻¹ − b⁻¹ = (b − a)/(ab)`
together with `|u − v| = |a − b|(a + b)` reduces the claim to `2c³ ≤ ab(a+b)`,
`c = √u₀`. -/
theorem abs_couplingOf_sub_le {u₀ u v : ℝ} (hu₀ : 0 < u₀) (hu : u₀ ≤ u) (hv : u₀ ≤ v) :
    |couplingOf u - couplingOf v| ≤ (1 / 2) * couplingOf u₀ ^ 3 * |u - v| := by
  have hupos : 0 < u := lt_of_lt_of_le hu₀ hu
  have hvpos : 0 < v := lt_of_lt_of_le hu₀ hv
  set c : ℝ := Real.sqrt u₀ with hc
  set a : ℝ := Real.sqrt u with ha
  set b : ℝ := Real.sqrt v with hb
  have hc0 : 0 < c := Real.sqrt_pos.mpr hu₀
  have ha0 : 0 < a := Real.sqrt_pos.mpr hupos
  have hb0 : 0 < b := Real.sqrt_pos.mpr hvpos
  have hac : c ≤ a := Real.sqrt_le_sqrt hu
  have hbc : c ≤ b := Real.sqrt_le_sqrt hv
  have hasq : a ^ 2 = u := Real.sq_sqrt hupos.le
  have hbsq : b ^ 2 = v := Real.sq_sqrt hvpos.le
  have hgu : couplingOf u = a⁻¹ := by rw [couplingOf, Real.sqrt_inv, ha]
  have hgv : couplingOf v = b⁻¹ := by rw [couplingOf, Real.sqrt_inv, hb]
  have hcube : couplingOf u₀ ^ 3 = (c ^ 3)⁻¹ := by
    rw [couplingOf, Real.sqrt_inv, inv_pow, hc]
  have hdiff : |couplingOf u - couplingOf v| = |a - b| / (a * b) := by
    rw [hgu, hgv]
    have hid : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by field_simp
    rw [hid, abs_div, abs_of_pos (show (0 : ℝ) < a * b by positivity), abs_sub_comm]
  have huv : |u - v| = |a - b| * (a + b) := by
    rw [← hasq, ← hbsq]
    have hid : a ^ 2 - b ^ 2 = (a - b) * (a + b) := by ring
    rw [hid, abs_mul, abs_of_pos (show (0 : ℝ) < a + b by positivity)]
  rw [hdiff, huv, hcube]
  have hRHS : 1 / 2 * (c ^ 3)⁻¹ * (|a - b| * (a + b))
      = (|a - b| * (a + b)) / (2 * c ^ 3) := by
    field_simp
  rw [hRHS, div_le_div_iff₀ (by positivity) (by positivity)]
  have hcc : c * c ≤ a * b := mul_le_mul hac hbc hc0.le (hc0.le.trans hac)
  have hsum : 2 * c ≤ a + b := by linarith
  have hprod : (c * c) * (2 * c) ≤ (a * b) * (a + b) :=
    mul_le_mul hcc hsum (by positivity) (by positivity)
  have hkey : 2 * c ^ 3 ≤ a * b * (a + b) := by nlinarith [hprod]
  nlinarith [hkey, abs_nonneg (a - b), ha0, hb0]

/-! ## 2. The weighted trajectory summation -/

/-- The exact telescoping comparison behind the weighted summation:
`(x+b)^{-3} ≤ (1/(2b))·[x^{-2} − (x+b)^{-2}]` for `x, b > 0`. -/
theorem inv_cube_le_telescope {x b : ℝ} (hx : 0 < x) (hb : 0 < b) :
    ((x + b) ^ 3)⁻¹ ≤ (1 / (2 * b)) * ((x ^ 2)⁻¹ - ((x + b) ^ 2)⁻¹) := by
  have hy : 0 < x + b := by linarith
  have hid : (1 / (2 * b)) * ((x ^ 2)⁻¹ - ((x + b) ^ 2)⁻¹) - ((x + b) ^ 3)⁻¹
      = b * (3 * x + b) / (2 * x ^ 2 * (x + b) ^ 3) := by
    field_simp
    ring
  have hnn : 0 ≤ (1 / (2 * b)) * ((x ^ 2)⁻¹ - ((x + b) ^ 2)⁻¹) - ((x + b) ^ 3)⁻¹ := by
    rw [hid]; positivity
  linarith

/-- The shifted (strictly positive index) part of the weighted sum telescopes
exactly. -/
theorem sum_inv_cube_shift_le {u₀ b : ℝ} (hu₀ : 0 < u₀) (hb : 0 < b) (M : ℕ) :
    ∑ i ∈ range M, ((u₀ + b * (i + 1)) ^ 3)⁻¹
      ≤ (1 / (2 * b)) * ((u₀ ^ 2)⁻¹ - ((u₀ + b * M) ^ 2)⁻¹) := by
  induction M with
  | zero => simp
  | succ n ih =>
      have hx : 0 < u₀ + b * n := by
        have : (0 : ℝ) ≤ b * n := by positivity
        linarith
      have hstep := inv_cube_le_telescope (x := u₀ + b * n) (b := b) hx hb
      have hcast : u₀ + b * n + b = u₀ + b * ((n : ℝ) + 1) := by ring
      rw [hcast] at hstep
      rw [Finset.sum_range_succ]
      push_cast
      linarith [ih, hstep]

/-- **The weighted sum of the cubes of the trajectory weights.**
`Σ_{j<K}(u₀+bj)^{-3} ≤ u₀^{-3} + 1/(2b u₀²)`.  The `j = 0` term is kept as it
stands and the tail is telescoped; no weight is replaced by its supremum, which
is what produces the `u₀⁻²` (rather than `u₀⁻¹`) gain. -/
theorem sum_inv_cube_linear_le {u₀ b : ℝ} (hu₀ : 0 < u₀) (hb : 0 < b) (K : ℕ) :
    ∑ j ∈ range K, ((u₀ + b * j) ^ 3)⁻¹ ≤ (u₀ ^ 3)⁻¹ + 1 / (2 * b * u₀ ^ 2) := by
  have hbase : (0 : ℝ) ≤ (u₀ ^ 3)⁻¹ := by positivity
  cases K with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
  | succ M =>
      rw [Finset.sum_range_succ']
      push_cast
      have h1 := sum_inv_cube_shift_le (u₀ := u₀) (b := b) hu₀ hb M
      have h2 : (0 : ℝ) ≤ ((u₀ + b * M) ^ 2)⁻¹ := by positivity
      have h3 : (1 / (2 * b)) * ((u₀ ^ 2)⁻¹ - ((u₀ + b * M) ^ 2)⁻¹)
          ≤ 1 / (2 * b * u₀ ^ 2) := by
        have hfac : (1 / (2 * b)) * (u₀ ^ 2)⁻¹ = 1 / (2 * b * u₀ ^ 2) := by
          field_simp
        have hmono : (1 / (2 * b)) * ((u₀ ^ 2)⁻¹ - ((u₀ + b * M) ^ 2)⁻¹)
            ≤ (1 / (2 * b)) * (u₀ ^ 2)⁻¹ := by
          have : (0 : ℝ) < 1 / (2 * b) := by positivity
          nlinarith [h2]
        linarith [hmono, hfac.le, hfac.ge]
      have hzero : ((u₀ + b * (0 : ℝ)) ^ 3)⁻¹ = (u₀ ^ 3)⁻¹ := by norm_num
      rw [hzero]
      linarith [h1, h3]

end YangMills
