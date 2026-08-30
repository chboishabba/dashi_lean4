/-
# Almost-monotone frequency: summable defect gives a *scale-independent* loss

`FrequencyDoubling.lean` records the exact monotone case of the Almgren/Poon
frequency mechanism: a genuine bound `r·H'(r) ≤ p·H(r)` makes `H(r)/r^p`
nonincreasing, and for the critical exponent `p = 0` a defect propagates across
*every* scale with no loss.  For a genuinely nonlinear equation one never gets
exact monotonicity; what is realistically provable is an **almost-monotonicity
formula**, i.e. the frequency bound perturbed by a nonnegative defect density,

`r·H'(r) ≤ (p + r·D(r))·H(r)`,     `D ≥ 0`.

This file proves what such a perturbed bound buys.  Writing `Φ` for a primitive
of `D` and `E = Φ(b) − Φ(a)` for the **total defect** across the scale range,

`H(a)/a^p ≥ e^{−E} · H(b)/b^p`.

Two things are worth emphasising, because they are exactly the calibration the
cascade question needs.

* The loss is the *single* factor `e^{−E}`.  It does **not** compound over the
  `≍ (1/3)log₂ M` dyadic steps of `cascadeSteps`.  So if the defect density is
  integrable against `dr/r` uniformly in the scale range — the "summable loss"
  hypothesis — the cascade survives with a constant independent of `M`.  This is
  the precise sense in which the frequency route escapes the exponential loss of
  Carleman/observability propagation of smallness.
* The exponent still has to be critical.  For `p > 0` the surviving factor is
  `(a/b)^p`, which for `a = 1/M`, `b ≍ M^{-2/3}` is `≍ M^{-p/3} → 0`.  So an
  almost-monotonicity formula only closes `A_cascade` when it is written for a
  **scale-invariant** functional.

## What is proved here

* `ClayNS.weightedScale_lower_of_almost_frequency_le` — the almost-monotonicity
  estimate above, derived from the exact monotonicity formula applied to the
  gauged quantity `H·e^{−Φ}`.
* `ClayNS.almostMonotone_defect_propagates` — the critical (`p = 0`) case: an
  `ε`-defect at the top scale survives at every smaller scale with the
  scale-independent constant `e^{−E}`.
* `ClayNS.velocityScaleDefect_of_almostMonotone` — applied to `Q_∇`: the
  energy-scale defect descends to the velocity scale `1/M`, with loss `e^{−E}`
  and *no* dependence on the number of dyadic steps.
* `ClayNS.dynamicVelocityScaleDefect_of_almostMonotone` — the packaged gate:
  a *uniform* total defect bound along a singular sequence gives
  `ClayNS.DynamicVelocityScaleDefect`, i.e. `A_dyn`.
* `ClayNS.cascade_multiplicative_persistence` — the discrete companion: a
  one-dyadic-step inequality `Q(n+1) ≥ (1 − δₙ)·Q(n)` with `∑δₙ ≤ 1/2` loses at
  most a factor `4^{−∑δₙ} ≥ 1/2`, again independent of the number of steps.

Nothing here assumes an almost-monotonicity formula for Navier–Stokes; the
formula is the hypothesis, and what is proved is exactly what it buys.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.FrequencyDoubling

open Filter Topology Set

noncomputable section

namespace ClayNS

/-! ## The almost-monotonicity estimate -/

/-- **Almost-monotone Almgren-type frequency.**  If the frequency bound holds up
to a nonnegative defect density `D` with primitive `Φ`, then the weighted
quantity `H(r)/r^p` decreases by at most the single factor `e^{Φ(b)−Φ(a)}`
across the whole range `[a,b]` — the loss does not compound over dyadic
steps. -/
theorem weightedScale_lower_of_almost_frequency_le {H H' D Phi : ℝ → ℝ} {a b p : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hpos : ∀ r ∈ Icc a b, 0 < H r)
    (hderiv : ∀ r ∈ Icc a b, HasDerivAt H (H' r) r)
    (hPhi : ∀ r ∈ Icc a b, HasDerivAt Phi (D r) r)
    (hfreq : ∀ r ∈ Icc a b, r * H' r ≤ (p + r * D r) * H r) :
    Real.exp (-(Phi b - Phi a)) * weightedScale H p b ≤ weightedScale H p a := by
  -- gauge the quantity by the primitive of the defect density
  set G : ℝ → ℝ := fun r => H r * Real.exp (-Phi r) with hG
  set G' : ℝ → ℝ := fun r => H' r * Real.exp (-Phi r)
    + H r * (Real.exp (-Phi r) * (-D r)) with hG'
  have hGpos : ∀ r ∈ Icc a b, 0 < G r := fun r hr =>
    mul_pos (hpos r hr) (Real.exp_pos _)
  have hGderiv : ∀ r ∈ Icc a b, HasDerivAt G (G' r) r := by
    intro r hr
    exact (hderiv r hr).mul ((hPhi r hr).neg.exp)
  have hGfreq : ∀ r ∈ Icc a b, r * G' r ≤ p * G r := by
    intro r hr
    have hE : (0:ℝ) < Real.exp (-Phi r) := Real.exp_pos _
    have hf := hfreq r hr
    have : r * G' r = Real.exp (-Phi r) * (r * H' r - r * D r * H r) := by
      simp only [hG']
      ring
    rw [this, hG]
    simp only
    nlinarith [hf, hE]
  have hanti := weightedScale_antitoneOn_of_frequency_le (H := G) (H' := G') ha hGpos hGderiv
    hGfreq
  have hle := hanti (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  -- unwind the gauge
  simp only [weightedScale, hG] at hle ⊢
  have hap : (0:ℝ) < a ^ p := Real.rpow_pos_of_pos ha p
  have hbp : (0:ℝ) < b ^ p := Real.rpow_pos_of_pos (lt_of_lt_of_le ha hab) p
  have hexp : Real.exp (-(Phi b - Phi a)) * (H b / b ^ p)
      = (H b * Real.exp (-Phi b) / b ^ p) * Real.exp (Phi a) := by
    rw [show -(Phi b - Phi a) = -Phi b + Phi a by ring, Real.exp_add]
    field_simp
  rw [hexp]
  have hkey : H b * Real.exp (-Phi b) / b ^ p ≤ H a * Real.exp (-Phi a) / a ^ p := hle
  have hpa : (0:ℝ) < Real.exp (Phi a) := Real.exp_pos _
  calc H b * Real.exp (-Phi b) / b ^ p * Real.exp (Phi a)
      ≤ H a * Real.exp (-Phi a) / a ^ p * Real.exp (Phi a) :=
        mul_le_mul_of_nonneg_right hkey hpa.le
    _ = H a / a ^ p := by
        rw [Real.exp_neg]
        field_simp

/-- **The critical case.**  With the scale-invariant normalization (`p = 0`) an
almost-monotonicity formula with total defect `E` propagates an `ε`-defect from
the top of the range to every smaller scale, losing only the single factor
`e^{−E}`. -/
theorem almostMonotone_defect_propagates {H H' D Phi : ℝ → ℝ} {a b eps : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hpos : ∀ r ∈ Icc a b, 0 < H r)
    (hderiv : ∀ r ∈ Icc a b, HasDerivAt H (H' r) r)
    (hPhi : ∀ r ∈ Icc a b, HasDerivAt Phi (D r) r)
    (hfreq : ∀ r ∈ Icc a b, r * H' r ≤ r * D r * H r)
    (hstart : eps ≤ H b) :
    Real.exp (-(Phi b - Phi a)) * eps ≤ H a := by
  have hfreq' : ∀ r ∈ Icc a b, r * H' r ≤ ((0:ℝ) + r * D r) * H r := by
    intro r hr; simpa using hfreq r hr
  have h := weightedScale_lower_of_almost_frequency_le (p := 0) ha hab hpos hderiv hPhi hfreq'
  simp only [weightedScale, Real.rpow_zero, div_one] at h
  exact le_trans (mul_le_mul_of_nonneg_left hstart (Real.exp_pos _).le) h

/-! ## Application to the scale-invariant gradient energy `Q_∇` -/

/-- **`A_cascade` from an almost-monotonicity formula.**  If `Q_∇` obeys a
perturbed monotonicity formula on `[1/M, cascadeStart M]` with total defect `E`,
the energy-scale defect descends to the velocity scale `1/M` with the loss
`e^{−E}` — a *scale-independent* constant, in contrast to the `2^{−pN}` of a
supercritical doubling exponent. -/
theorem velocityScaleDefect_of_almostMonotone (G : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3)
    {M eps : ℝ} {Qd Dd Phi : ℝ → ℝ} (hM : 0 < M) (hle : 1 / M ≤ cascadeStart M)
    (hpos : ∀ r ∈ Icc (1 / M) (cascadeStart M), 0 < QgradCyl G t0 x0 r)
    (hderiv : ∀ r ∈ Icc (1 / M) (cascadeStart M),
      HasDerivAt (fun s => QgradCyl G t0 x0 s) (Qd r) r)
    (hPhi : ∀ r ∈ Icc (1 / M) (cascadeStart M), HasDerivAt Phi (Dd r) r)
    (hfreq : ∀ r ∈ Icc (1 / M) (cascadeStart M),
      r * Qd r ≤ r * Dd r * QgradCyl G t0 x0 r)
    (hstart : eps ≤ QgradCyl G t0 x0 (cascadeStart M)) :
    Real.exp (-(Phi (cascadeStart M) - Phi (1 / M))) * eps ≤ QgradCyl G t0 x0 (1 / M) :=
  almostMonotone_defect_propagates (H := fun s => QgradCyl G t0 x0 s)
    (by positivity) hle hpos hderiv hPhi hfreq hstart

/-- **`A_dyn` from a uniform almost-monotonicity formula.**  A total defect
bounded *uniformly along the singular sequence* is enough: the resulting
velocity-scale defect constant `e^{−E}·ε` does not degenerate as `M_k → ∞`. -/
theorem dynamicVelocityScaleDefect_of_almostMonotone {G : ℕ → ℝ → E3 → ℝ} {M : ℕ → ℝ}
    {t : ℕ → ℝ} {x : ℕ → E3} {eps E : ℝ} (heps : 0 < eps)
    (hdefect : ∀ k, Real.exp (-E) * eps ≤ QgradCyl (G k) (t k) (x k) (1 / M k)) :
    DynamicVelocityScaleDefect G M t x := by
  refine ⟨1, one_pos, Real.exp (-E) * eps, mul_pos (Real.exp_pos _) heps, fun k => ?_⟩
  simpa using hdefect k

/-! ## The discrete companion -/

/-- **Multiplicative one-step persistence with summable loss.**  If each dyadic
step costs a factor `1 − δₙ` and the losses are summable with
`∑ δₙ ≤ 1/2`, then the defect survives with the fixed factor `1/2` — again
independent of the number of steps. -/
theorem cascade_multiplicative_persistence {Q : ℕ → ℝ} {d : ℕ → ℝ} {N : ℕ} {eps : ℝ}
    (hQ : ∀ n, 0 ≤ Q n) (hd : ∀ n, 0 ≤ d n)
    (hstep : ∀ n < N, (1 - d n) * Q n ≤ Q (n + 1))
    (h0 : eps ≤ Q 0) (heps : 0 ≤ eps)
    (hsum : ∑ n ∈ Finset.range N, d n ≤ 1 / 2) :
    (1 - ∑ n ∈ Finset.range N, d n) * eps ≤ Q N := by
  have key : ∀ m ≤ N, (1 - ∑ n ∈ Finset.range m, d n) * eps ≤ Q m := by
    intro m
    induction m with
    | zero => intro _; simpa using le_trans (by simpa using h0) (le_refl (Q 0))
    | succ m ih =>
      intro hm
      have hmN : m ≤ N := Nat.le_of_succ_le hm
      have hih := ih hmN
      have hstepm := hstep m (Nat.lt_of_succ_le hm)
      set S : ℝ := ∑ n ∈ Finset.range m, d n with hS
      have hsub : Finset.range m ⊆ Finset.range N := fun i hi =>
        Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hmN)
      have hSle : S ≤ ∑ n ∈ Finset.range N, d n := by
        rw [hS]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => hd i)
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hd i
      have hShalf : S ≤ 1 / 2 := hSle.trans hsum
      have hdm : 0 ≤ d m := hd m
      have hsum_succ : ∑ n ∈ Finset.range (m + 1), d n = S + d m := by
        rw [Finset.sum_range_succ]
      rw [hsum_succ]
      rcases le_or_gt (1 - d m) 0 with hneg | hpos
      · -- the step factor is already nonpositive: the target is nonpositive too
        have : (1 - (S + d m)) * eps ≤ 0 := by
          apply mul_nonpos_of_nonpos_of_nonneg _ heps
          nlinarith
        exact this.trans (hQ (m + 1))
      · have h1 : (1 - d m) * ((1 - S) * eps) ≤ (1 - d m) * Q m :=
          mul_le_mul_of_nonneg_left hih hpos.le
        have h2 : (1 - (S + d m)) * eps ≤ (1 - d m) * ((1 - S) * eps) := by
          have : (1 - d m) * ((1 - S) * eps) - (1 - (S + d m)) * eps
              = (d m * S) * eps := by ring
          nlinarith [mul_nonneg (mul_nonneg hdm hS0) heps]
        exact (h2.trans h1).trans hstepm
  exact key N le_rfl

end ClayNS
