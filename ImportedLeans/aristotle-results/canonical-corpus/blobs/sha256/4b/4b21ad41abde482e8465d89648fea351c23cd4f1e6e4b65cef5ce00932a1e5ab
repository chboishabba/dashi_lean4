/-
# Almgren-type frequency bounds, doubling, and the zero-loss cascade

`DyadicCascade.lean` isolates the exact shape a one-dyadic-step lemma must have
in order to carry a defect from the energy scale `M^{-2/3}` to the velocity
scale `M^{-1}`: **zero loss** (a monotone scale-critical quantity) or a loss
that is *summable in the step index*.  This file supplies the classical
mechanism that produces exactly such statements — the Almgren/Poon frequency
function and the doubling inequality it implies — in the abstract form in which
it is actually used, and then plugs it into the cascade.

## What is proved here

* `ClayNS.weightedScale H p r = H r / r ^ p` and
  `ClayNS.weightedScale_antitoneOn_of_frequency_le` — the **monotonicity
  formula in abstract form**: if `H > 0` is differentiable on `[a,b] ⊆ (0,∞)`
  and its logarithmic derivative obeys the frequency bound
  `r·H'(r) ≤ p·H(r)`, then `r ↦ H r / r^p` is nonincreasing on `[a,b]`.
  (For the Almgren frequency `N(r) = r∫_{B_r}|∇u|²/∫_{∂B_r}u²` in dimension `n`
  the classical identity is `r·H'(r) = (n−1+2N(r))·H(r)`, so `p = n−1+2N₀` for
  any upper bound `N₀` on the frequency.)
* `ClayNS.doubling_of_frequency_le` — the resulting doubling inequality
  `H(2r) ≤ 2^p·H(r)`: the loss across a dyadic step is the **fixed factor**
  `2^{-p}`, polynomial in the scale ratio rather than exponential.  This is the
  precise sense in which the frequency route avoids the exponential loss of
  Carleman-based propagation of smallness.
* `ClayNS.frequency_cascade_guarantee_tendsto_zero` — but a *fixed* factor is
  still fatal over `≍ log M` steps: for `p > 0` the guarantee `2^{-pN}ε`
  degenerates as `M → ∞`.  So a doubling inequality with a **strictly
  supercritical** exponent does not close `A_cascade` either.
* `ClayNS.weightedScale_defect_propagates` — the **zero-loss case**: with the
  critical exponent (i.e. for the *scale-invariant* normalization of the defect
  functional, `p = 0` after normalizing) the monotonicity formula propagates the
  defect to *every* smaller radius, with no loss at all and with no dependence
  on the number of steps.
* `ClayNS.velocityScaleDefect_of_scaleAntitone` — applied to `Q_∇`: an
  energy-scale defect plus antitonicity of `r ↦ Q_∇(r)` on
  `[1/M, cascadeStart M]` gives the velocity-scale defect with the *same*
  constant, i.e. exactly the gate `A_dyn`.
* `ClayNS.velocityScaleDefect_of_dyadic_cascade` — the summable-loss version:
  a one-dyadic-step persistence inequality with total loss `≤ ε/2` gives the
  velocity-scale defect with constant `ε/2`.
* `ClayNS.dynamicVelocityScaleDefect_of_cascade` — the packaged statement:
  along a singular sequence, energy-scale defect + one-step persistence with
  summable loss ⟹ `ClayNS.DynamicVelocityScaleDefect` (the gate `A_dyn`) with
  `c = 1`.

Nothing here assumes the frequency bound for Navier–Stokes; the bound is the
hypothesis, and what is proved is exactly what it buys.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.DyadicCascade
import RequestProject.NavierStokes.DynamicDefectReduction

open Filter Topology Set

noncomputable section

namespace ClayNS

/-! ## The abstract monotonicity formula -/

/-- The scale-weighted quantity `H(r)/r^p`.  For `p` the natural scaling
exponent of `H` this is the scale-invariant normalization. -/
def weightedScale (H : ℝ → ℝ) (p r : ℝ) : ℝ := H r / r ^ p

/-- **Abstract Almgren-type monotonicity.**  A frequency bound on the
logarithmic derivative, `r·H'(r) ≤ p·H(r)`, makes the weighted quantity
`H(r)/r^p` nonincreasing. -/
theorem weightedScale_antitoneOn_of_frequency_le {H H' : ℝ → ℝ} {a b p : ℝ}
    (ha : 0 < a)
    (hpos : ∀ r ∈ Icc a b, 0 < H r)
    (hderiv : ∀ r ∈ Icc a b, HasDerivAt H (H' r) r)
    (hfreq : ∀ r ∈ Icc a b, r * H' r ≤ p * H r) :
    AntitoneOn (fun r => weightedScale H p r) (Icc a b) := by
  set g : ℝ → ℝ := fun r => Real.log (H r) - p * Real.log r with hg
  have hrpos : ∀ r ∈ Icc a b, 0 < r := fun r hr => lt_of_lt_of_le ha hr.1
  have hgderiv : ∀ r ∈ Icc a b, HasDerivAt g (H' r / H r - p / r) r := by
    intro r hr
    have h1 : HasDerivAt (fun r => Real.log (H r)) (H' r / H r) r :=
      (hderiv r hr).log (ne_of_gt (hpos r hr))
    have h2 : HasDerivAt (fun r : ℝ => p * Real.log r) (p * r⁻¹) r :=
      (Real.hasDerivAt_log (ne_of_gt (hrpos r hr))).const_mul p
    have := h1.sub h2
    simpa [hg, div_eq_mul_inv] using this
  have hgnonpos : ∀ r ∈ Ioo a b, deriv g r ≤ 0 := by
    intro r hr
    have hrI : r ∈ Icc a b := ⟨hr.1.le, hr.2.le⟩
    have hd := hgderiv r hrI
    have hrp := hrpos r hrI
    have hHp := hpos r hrI
    have hfr := hfreq r hrI
    have : H' r / H r - p / r ≤ 0 := by
      rw [sub_nonpos, div_le_div_iff₀ hHp hrp]
      nlinarith [hfr]
    rw [hd.deriv]
    exact this
  have hcont : ContinuousOn g (Icc a b) := by
    intro r hr
    have h1 : ContinuousAt (fun r => Real.log (H r)) r :=
      (Real.continuousAt_log (ne_of_gt (hpos r hr))).comp (hderiv r hr).continuousAt
    have h2 : ContinuousAt (fun r : ℝ => p * Real.log r) r :=
      (Real.continuousAt_log (ne_of_gt (hrpos r hr))).const_smul p
    exact ((h1.sub h2)).continuousWithinAt
  have hdiff : ∀ r ∈ Ioo a b, DifferentiableAt ℝ g r := fun r hr =>
    (hgderiv r ⟨hr.1.le, hr.2.le⟩).differentiableAt
  have hganti : AntitoneOn g (Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont ?_ ?_
    · intro r hr
      rw [interior_Icc] at hr
      exact (hdiff r hr).differentiableWithinAt
    · intro r hr
      rw [interior_Icc] at hr
      exact hgnonpos r hr
  intro x hx y hy hxy
  have hgxy : g y ≤ g x := hganti hx hy hxy
  have hex : ∀ r ∈ Icc a b, weightedScale H p r = Real.exp (g r) := by
    intro r hr
    have hrp := hrpos r hr
    have hHp := hpos r hr
    rw [hg]
    simp only
    rw [Real.exp_sub, Real.exp_log hHp, ← Real.log_rpow hrp p, Real.exp_log
      (Real.rpow_pos_of_pos hrp p)]
    rfl
  show weightedScale H p y ≤ weightedScale H p x
  rw [hex y hy, hex x hx]
  exact Real.exp_le_exp.mpr hgxy

/-- **Doubling.**  The frequency bound gives `H(2r) ≤ 2^p H(r)`: the loss across
a dyadic step is the fixed factor `2^{-p}` — polynomial in the scale ratio, not
exponential. -/
theorem doubling_of_frequency_le {H H' : ℝ → ℝ} {r p : ℝ} (hr : 0 < r)
    (hpos : ∀ s ∈ Icc r (2 * r), 0 < H s)
    (hderiv : ∀ s ∈ Icc r (2 * r), HasDerivAt H (H' s) s)
    (hfreq : ∀ s ∈ Icc r (2 * r), s * H' s ≤ p * H s) :
    H (2 * r) ≤ 2 ^ p * H r := by
  have hab : r ≤ 2 * r := by linarith
  have hanti := weightedScale_antitoneOn_of_frequency_le hr hpos hderiv hfreq
  have hle := hanti (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab) hab
  simp only [weightedScale] at hle
  have hrp : (0:ℝ) < r ^ p := Real.rpow_pos_of_pos hr p
  have h2rp : (0:ℝ) < (2 * r) ^ p := Real.rpow_pos_of_pos (by linarith) p
  have hsplit : (2 * r) ^ p = 2 ^ p * r ^ p :=
    Real.mul_rpow (by norm_num) hr.le
  rw [div_le_div_iff₀ h2rp hrp, hsplit] at hle
  have h2p : (0:ℝ) < (2:ℝ) ^ p := Real.rpow_pos_of_pos (by norm_num) p
  nlinarith [hle, hrp, h2p]

/-- **A supercritical doubling exponent is still fatal.**  For `p > 0` the
dyadic loss factor is `2^{-p} < 1`, so over the `cascadeSteps M ≍ (1/3)log₂ M`
steps of the cascade the guaranteed defect `2^{-pN}ε` tends to `0`.  Only the
*critical* (zero-loss) normalization survives. -/
theorem frequency_cascade_guarantee_tendsto_zero {p eps : ℝ} (hp : 0 < p) :
    Tendsto (fun M : ℝ => ((2:ℝ) ^ (-p)) ^ cascadeSteps M * eps) atTop (𝓝 0) := by
  have hc1 : (2:ℝ) ^ (-p) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hc0 : (0:ℝ) ≤ (2:ℝ) ^ (-p) := (Real.rpow_pos_of_pos (by norm_num) _).le
  exact geometric_guarantee_tendsto_zero hc0 hc1

/-- **The zero-loss cascade.**  With the critical weight the monotonicity
formula propagates a defect to *every* smaller radius in the range, with no loss
and with no dependence on the number of dyadic steps. -/
theorem weightedScale_defect_propagates {H H' : ℝ → ℝ} {a b p eps : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hpos : ∀ r ∈ Icc a b, 0 < H r)
    (hderiv : ∀ r ∈ Icc a b, HasDerivAt H (H' r) r)
    (hfreq : ∀ r ∈ Icc a b, r * H' r ≤ p * H r)
    (hstart : eps ≤ weightedScale H p b) :

    ∀ r ∈ Icc a b, eps ≤ weightedScale H p r := by
  intro r hr
  have := weightedScale_antitoneOn_of_frequency_le ha hpos hderiv hfreq hr
    (right_mem_Icc.mpr hab) hr.2
  exact hstart.trans this

/-! ## Application to the scale-invariant gradient energy `Q_∇` -/

/-- **The zero-loss form of `A_cascade` for `Q_∇`.**  `Q_∇` is already
scale-invariant, so the critical weight is `p = 0` and the monotonicity formula
is literally antitonicity of `r ↦ Q_∇(r)`.  Under it, the energy-scale defect
descends to the velocity scale `1/M` with the *same* constant. -/
theorem velocityScaleDefect_of_scaleAntitone (G : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3)
    {M eps : ℝ} (hle : 1 / M ≤ cascadeStart M)
    (hanti : AntitoneOn (fun r => QgradCyl G t0 x0 r) (Icc (1 / M) (cascadeStart M)))
    (hstart : eps ≤ QgradCyl G t0 x0 (cascadeStart M)) :
    eps ≤ QgradCyl G t0 x0 (1 / M) :=
  hstart.trans (hanti (left_mem_Icc.mpr hle) (right_mem_Icc.mpr hle) hle)

/-- **The summable-loss form of `A_cascade` for `Q_∇`.**  A one-dyadic-step
persistence inequality along the radii `cascadeStart M · 2^{-n}`, whose total
loss over the `cascadeSteps M` steps is at most `ε/2`, delivers a defect of size
`ε/2` at exactly the velocity scale `1/M`. -/
theorem velocityScaleDefect_of_dyadic_cascade (G : ℝ → E3 → ℝ) (t0 : ℝ) (x0 : E3)
    {M eps : ℝ} (hM : 0 < M) (b : ℕ → ℝ)
    (hstart : eps ≤ QgradCyl G t0 x0 (cascadeStart M))
    (hstep : ∀ n < cascadeSteps M,
      QgradCyl G t0 x0 (cascadeStart M / 2 ^ n) - b n
        ≤ QgradCyl G t0 x0 (cascadeStart M / 2 ^ (n + 1)))
    (hsum : ∑ n ∈ Finset.range (cascadeSteps M), b n ≤ eps / 2) :
    eps / 2 ≤ QgradCyl G t0 x0 (1 / M) := by
  set Q : ℕ → ℝ := fun n => QgradCyl G t0 x0 (cascadeStart M / 2 ^ n) with hQ
  have h0 : eps ≤ Q 0 := by simpa [hQ] using hstart
  have hN : Q (cascadeSteps M) = QgradCyl G t0 x0 (1 / M) := by
    rw [hQ]
    simp only
    rw [cascadeStart_div_pow hM]
  have := cascade_persistence_of_small_total_loss (Q := Q) (b := b)
    (N := cascadeSteps M) (eps := eps) (fun n hn => hstep n hn) h0 hsum
  rwa [hN] at this

/-- **`A_dyn` from the cascade.**  Along a singular sequence, an energy-scale
defect together with a one-dyadic-step persistence inequality of summable loss
yields the velocity-scale defect gate `ClayNS.DynamicVelocityScaleDefect`, with
`c = 1`: the defect sits at radius exactly `1/M_k`. -/
theorem dynamicVelocityScaleDefect_of_cascade {G : ℕ → ℝ → E3 → ℝ} {M : ℕ → ℝ} {t : ℕ → ℝ}
    {x : ℕ → E3} {eps : ℝ} (heps : 0 < eps) (hM : ∀ k, 0 < M k) (b : ℕ → ℕ → ℝ)
    (hstart : ∀ k, eps ≤ QgradCyl (G k) (t k) (x k) (cascadeStart (M k)))
    (hstep : ∀ k, ∀ n < cascadeSteps (M k),
      QgradCyl (G k) (t k) (x k) (cascadeStart (M k) / 2 ^ n) - b k n
        ≤ QgradCyl (G k) (t k) (x k) (cascadeStart (M k) / 2 ^ (n + 1)))
    (hsum : ∀ k, ∑ n ∈ Finset.range (cascadeSteps (M k)), b k n ≤ eps / 2) :
    DynamicVelocityScaleDefect G M t x := by
  refine ⟨1, one_pos, eps / 2, by linarith, fun k => ?_⟩
  have h := velocityScaleDefect_of_dyadic_cascade (G k) (t k) (x k) (hM k) (b k)
    (hstart k) (hstep k) (hsum k)
  simpa using h

end ClayNS
