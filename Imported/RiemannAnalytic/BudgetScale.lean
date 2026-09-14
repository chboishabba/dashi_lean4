/-
**Which budgets can close the tube, and which cannot.**

`GramBudgetTransport.lean` shows that a budget `E(T)` for the weighted zero-pair
Gram sum confines every transverse offset to `|α| ≤ √(E(T)/(c L(T)⁶))`, and that
the tube closes exactly when `E(T)/L(T)⁶ → 0`.  The taper scale of the source is
logarithmic, `L(T) = λ log T`, so the tube closes only for budgets of size
`o((log T)⁶)`.

This file records the resulting *scale test*, in both directions:

* `budget_ratio_tendsto_atTop`: if the budget is at least `κ·T·L(T)²` — that is,
  if it carries even one power of `T` — then `E(T)/L(T)⁶ → ∞`;
* `not_tendsto_zero_of_linear_growth` and `tube_radius_tendsto_atTop`: the tube
  then does not close, its radius diverges.

This is the quantitative form of the observation that the *total* exterior area
of the full evaluation family is far larger than the per-zero floor: a budget
obtained by bounding the total area of a `d × d` Gram matrix, `d ≍ L T/2π`,
is polynomial in `T`, whereas the zero-side floor `c L⁶ α²` is only
polylogarithmic.  Any route that feeds a total-area estimate into the tube
theorem therefore fails the scale test, and a localized budget — one attached to
a bounded number of zeros — is needed instead.

Nothing here refers to `ζ`; `L`, `E` are arbitrary functions and every growth
statement is a hypothesis.
-/
import RiemannAnalytic.GramBudgetTransport

namespace RiemannAnalytic

open Filter Topology

/-- `T / (log T)⁴ → ∞`. -/
theorem tendsto_id_div_log_pow_four :
    Tendsto (fun T : ℝ => T / Real.log T ^ 4) atTop atTop := by
  have h : Tendsto (fun T : ℝ => Real.log T ^ 4 / T) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hl : 0 < Real.log T := Real.log_pos hT
    simp only [Set.mem_Ioi]
    positivity
  have h2 := tendsto_inv_nhdsGT_zero.comp h
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have hl : 0 < Real.log T := Real.log_pos hT
  simp [Function.comp, inv_div]

/-- **The scale test.**  With a logarithmic taper scale `L(T) = λ log T`, a
budget carrying a power of `T` makes the normalized budget diverge:

    E(T) ≥ κ · T · L(T)²   ⟹   E(T)/L(T)⁶ → ∞. -/
theorem budget_ratio_tendsto_atTop {Ebud L : ℝ → ℝ} {κ lam : ℝ} (hκ : 0 < κ) (hlam : 0 < lam)
    (hL : ∀ T, L T = lam * Real.log T)
    (hE : ∀ᶠ T in atTop, κ * T * L T ^ 2 ≤ Ebud T) :
    Tendsto (fun T => Ebud T / L T ^ 6) atTop atTop := by
  have hbase : Tendsto (fun T : ℝ => κ / lam ^ 4 * (T / Real.log T ^ 4)) atTop atTop := by
    refine Tendsto.const_mul_atTop (by positivity) tendsto_id_div_log_pow_four
  refine tendsto_atTop_mono' atTop ?_ hbase
  filter_upwards [hE, eventually_gt_atTop (1 : ℝ)] with T hET hT
  have hl : 0 < Real.log T := Real.log_pos hT
  have hLpos : 0 < L T := by rw [hL T]; positivity
  have hL6 : (0 : ℝ) < L T ^ 6 := by positivity
  have hstep : κ / lam ^ 4 * (T / Real.log T ^ 4) = κ * T * L T ^ 2 / L T ^ 6 := by
    rw [hL T]
    field_simp
  rw [hstep]
  exact (div_le_div_iff_of_pos_right hL6).mpr hET

/-- Consequently the normalized budget does not tend to zero, so the tube
criterion of `GramBudgetTransport.lean` is not met. -/
theorem not_tendsto_zero_of_linear_growth {Ebud L : ℝ → ℝ} {κ lam : ℝ} (hκ : 0 < κ)
    (hlam : 0 < lam) (hL : ∀ T, L T = lam * Real.log T)
    (hE : ∀ᶠ T in atTop, κ * T * L T ^ 2 ≤ Ebud T) :
    ¬ Tendsto (fun T => Ebud T / L T ^ 6) atTop (𝓝 0) :=
  not_tendsto_nhds_of_tendsto_atTop (budget_ratio_tendsto_atTop hκ hlam hL hE) 0

/-- The tube radius itself diverges: such a budget confines nothing. -/
theorem tube_radius_tendsto_atTop {Ebud L : ℝ → ℝ} {κ lam c : ℝ} (hκ : 0 < κ) (hc : 0 < c)
    (hlam : 0 < lam) (hL : ∀ T, L T = lam * Real.log T)
    (hE : ∀ᶠ T in atTop, κ * T * L T ^ 2 ≤ Ebud T) :
    Tendsto (fun T => Real.sqrt (Ebud T / (c * L T ^ 6))) atTop atTop := by
  have hbase := budget_ratio_tendsto_atTop hκ hlam hL hE
  have hscaled : Tendsto (fun T => c⁻¹ * (Ebud T / L T ^ 6)) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity) hbase
  have hcongr : Tendsto (fun T => Ebud T / (c * L T ^ 6)) atTop atTop := by
    refine hscaled.congr fun T => ?_
    rw [div_const_mul _ _ hc.ne']
  exact Real.tendsto_sqrt_atTop.comp hcongr

end RiemannAnalytic
