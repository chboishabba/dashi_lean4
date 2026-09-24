/-
**Q9 — the scale test for the bounded-height budget, and what a shrinking tube
does and does not prove.**

`BudgetScale.lean` showed that a *global* budget carrying a power of `T` can
never satisfy the tube criterion `E(T)/L(T)⁶ → 0`.  The bounded-height repair
removes the power of `T`; the question is what it leaves.  The route is

    ∑_ρ m_ρ² Δ_ρ ≤ e₂(G_W^mult) ≤ ½ (tr G_W^mult)² ≤ 2 N_mult(W)² B(T)² ,

with `N_mult(W) ≍ L` zeros with multiplicity in a unit window (Riemann–von
Mangoldt) and `B(T)` the per-vector squared-norm scale.  Everything therefore
turns on `B`:

* `linear_scale_ratio_tendsto_zero` — **if** `B ≍ L` (the scale the programme
  assumed), the budget is `≍ L⁴`, the ratio `E/L⁶ ≍ L⁻² → 0`, and the tube
  closes;
* `quadratic_scale_ratio_eq_const` and `quadratic_scale_not_tendsto_zero` — with
  the *actual* scale `B ≍ L²` proved in `LocalTraceScale.lean`, the budget is
  `≍ L⁶`, the ratio is a positive constant, and the tube does **not** close;
* `quadratic_scale_tube_radius_const` — the resulting tube radius is a constant
  independent of `T`: bounded height removes the power of `T` and lands exactly
  at the order of the zero-side floor, critically rather than with room.

The second half of the file separates two statements that must not be conflated,
as the localization programme itself insists:

* `fixed_offset_eq_zero_of_eventual_tube` — a *fixed* offset confined to a
  shrinking tube for arbitrarily large scale parameters is zero;
* `exists_nonzero_offsets_within_shrinking_tube` — but a *family* of offsets,
  one per height, can satisfy a shrinking tube with **every member nonzero**.
  So "every high zero lies in a tube of radius `r(T) → 0`" gives
  `β_ρ − ½ = o(1)` as `γ_ρ → ∞` and does *not* by itself give `β_ρ = ½`.

Nothing here refers to `ζ`; `L`, `N`, `B` are arbitrary functions.
-/
import RiemannAnalytic.LocalTraceScale
import RiemannAnalytic.BudgetScale

namespace RiemannAnalytic

open Filter Topology

/-! ### The scale test for the local budget -/

/-- The budget produced by the norm-and-count route: `2 N² B²`. -/
noncomputable def localNormCountBudget (N B : ℝ) : ℝ := 2 * N ^ 2 * B ^ 2

/-- **The assumed (linear) scale closes the tube.**  If the per-vector squared
norm were of order `L` and the window contains `O(L)` zeros with multiplicity,
the budget would be of order `L⁴` and the normalized budget would vanish. -/
theorem linear_scale_ratio_tendsto_zero {L : ℝ → ℝ} {A Cb lam : ℝ} (hlam : 0 < lam)
    (hL : ∀ T, L T = lam * Real.log T) :
    Tendsto (fun T => localNormCountBudget (A * L T) (Cb * L T) / L T ^ 6) atTop (𝓝 0) := by
  have hbase : Tendsto (fun T : ℝ => 2 * A ^ 2 * Cb ^ 2 / (lam ^ 2 * Real.log T ^ 2))
      atTop (𝓝 0) := by
    have hlog2 : Tendsto (fun T : ℝ => Real.log T ^ 2) atTop atTop :=
      (Real.tendsto_log_atTop.atTop_mul_atTop₀ Real.tendsto_log_atTop).congr fun T => by ring
    have hden : Tendsto (fun T : ℝ => lam ^ 2 * Real.log T ^ 2) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity) hlog2
    exact Tendsto.div_atTop tendsto_const_nhds hden
  refine hbase.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hLT : L T = lam * Real.log T := hL T
  have hLpos : 0 < L T := by rw [hLT]; positivity
  unfold localNormCountBudget
  rw [hLT]
  field_simp

/-- **The actual (quadratic) scale gives a constant ratio.**  With the per-vector
squared-norm scale `B ≍ L²` — the one proved for the source vectors in
`LocalTraceScale.lean` — the normalized local budget is the constant `2A²Cb²`. -/
theorem quadratic_scale_ratio_eq_const {L : ℝ} (hL : L ≠ 0) (A Cb : ℝ) :
    localNormCountBudget (A * L) (Cb * L ^ 2) / L ^ 6 = 2 * A ^ 2 * Cb ^ 2 := by
  unfold localNormCountBudget
  field_simp

/-- Consequently the tube criterion fails: the normalized budget does not tend to
zero.  Bounded height removes the power of `T` of `BudgetScale.lean`, but with
the true trace scale it lands exactly at the order `L⁶` of the zero-side floor. -/
theorem quadratic_scale_not_tendsto_zero {L : ℝ → ℝ} {A Cb : ℝ} (hA : A ≠ 0) (hCb : Cb ≠ 0)
    (hL : ∀ᶠ T in atTop, L T ≠ 0) :
    ¬ Tendsto (fun T => localNormCountBudget (A * L T) (Cb * L T ^ 2) / L T ^ 6) atTop (𝓝 0) := by
  intro hten
  have hconst : Tendsto (fun _ : ℝ => 2 * A ^ 2 * Cb ^ 2) atTop (𝓝 0) := by
    refine hten.congr' ?_
    filter_upwards [hL] with T hT
    exact quadratic_scale_ratio_eq_const hT A Cb
  have hlim : (0 : ℝ) = 2 * A ^ 2 * Cb ^ 2 :=
    tendsto_nhds_unique hconst tendsto_const_nhds
  have hpos : (0 : ℝ) < 2 * A ^ 2 * Cb ^ 2 := by positivity
  linarith

/-- The tube radius from the local norm-and-count budget at the true trace scale
is a constant, independent of `T`: no localization gain in the offset. -/
theorem quadratic_scale_tube_radius_const {L c : ℝ} (hL : L ≠ 0) (hc : 0 < c) (A Cb : ℝ) :
    Real.sqrt (localNormCountBudget (A * L) (Cb * L ^ 2) / (c * L ^ 6))
      = Real.sqrt (2 * A ^ 2 * Cb ^ 2 / c) := by
  congr 1
  rw [div_const_mul _ _ hc.ne', quadratic_scale_ratio_eq_const hL A Cb]
  ring

/-! ### A shrinking tube is not the critical line -/

/-- **A fixed offset in a shrinking tube is zero.**  If one and the same offset
`α` is confined by radii tending to zero, it vanishes.  This is the case in
which a localization theorem does prove criticality — it needs the *same* zero
to be placed in windows with arbitrarily large scale parameter. -/
theorem fixed_offset_eq_zero_of_eventual_tube {α : ℝ} {r : ℝ → ℝ}
    (hr : Tendsto r atTop (𝓝 0)) (htube : ∀ᶠ T in atTop, |α| ≤ r T) : α = 0 := by
  by_contra hne
  have hpos : 0 < |α| := abs_pos.2 hne
  have hev : ∀ᶠ T in atTop, r T < |α| := by
    have := hr (Iio_mem_nhds hpos)
    simpa [Set.mem_Iio] using this
  obtain ⟨T, hT1, hT2⟩ := (htube.and hev).exists
  linarith

/-- **But a family of offsets in a shrinking tube need not vanish.**  There is a
family of *nonzero* offsets, one for each height, confined by radii tending to
zero.  Hence "every zero of height `T` lies in a tube of radius `r(T) → 0`"
yields only `β_ρ − ½ = o(1)` as the height grows, never `β_ρ = ½`. -/
theorem exists_nonzero_offsets_within_shrinking_tube :
    ∃ α r : ℝ → ℝ, (∀ T, 0 < r T) ∧ Tendsto r atTop (𝓝 0) ∧
      (∀ T, |α T| ≤ r T) ∧ ∀ T, α T ≠ 0 := by
  refine ⟨fun T => Real.exp (-T) / 2, fun T => Real.exp (-T), fun T => Real.exp_pos _, ?_, ?_, ?_⟩
  · exact Real.tendsto_exp_neg_atTop_nhds_zero
  · intro T
    have h := Real.exp_pos (-T)
    rw [abs_of_pos (by positivity)]
    linarith
  · intro T
    have h := Real.exp_pos (-T)
    positivity

end RiemannAnalytic
