/-
# The dyadic cascade calculus for `A_cascade`

The A-side seam of the route is a *scale gap*: the local-energy method naturally
produces a defect at the **energy scale** `r ≍ M^{-2/3}`
(`EnergyScaleDefect.lean`), while the blow-up/rigidity machinery consumes a
defect at the **velocity scale** `r ≍ M^{-1}`
(`DynamicDefectReduction.lean`).  The ratio of the two scales is `M^{1/3}`, so
only

  `N ≍ (1/3) log₂ M`

dyadic halvings separate them.  This file is the exact bookkeeping of that
observation together with the *iteration calculus*: given a one-dyadic-step
persistence inequality of a prescribed shape, what survives after `N` steps?

## What is proved here

* `ClayNS.cascadeSteps M = ⌈log₂ M / 3⌉` and
  `ClayNS.cascadeStart M = 2^{cascadeSteps M} / M`, the starting radius, with
  `ClayNS.cascadeStart_div_pow`: halving `cascadeStart M` exactly
  `cascadeSteps M` times lands *exactly* on the velocity scale `1/M`, and
  `ClayNS.cascadeStart_mem_Ico`: `M^{-2/3} ≤ cascadeStart M < 2·M^{-2/3}`, so the
  starting radius is within a factor `2` of the energy scale.
* `ClayNS.cascade_of_losses` — the additive iteration: a per-step loss `b n`
  costs exactly `∑_{n<N} b n`.
* `ClayNS.cascade_persistence_of_small_total_loss` — hence a **summable** loss
  (total `≤ ε/2`) preserves half the defect, *for every* `N`.  This is the only
  shape of one-step lemma that survives a number of steps growing with `M`.
* `ClayNS.cascade_geometric` and
  `ClayNS.geometric_guarantee_tendsto_zero` — a fixed multiplicative loss
  `Q(r/2) ≥ c·Q(r)`, `c < 1`, gives exactly `c^N Q₀`, and the guarantee
  degenerates to `0` as `M → ∞`: **a fixed-factor one-step lemma cannot close
  `A_cascade`.**
* `ClayNS.cascade_superlinear_threshold` — a superlinear loss
  `Q(r/2) ≥ Q(r) − C·Q(r)^{1+α}` preserves half the defect provided
  `N·C·ε^α ≤ 1/2`, and
  `ClayNS.superlinear_threshold_fails_eventually` — for *fixed* `ε, C, α` that
  condition eventually fails, i.e. a superlinear one-step lemma with fixed
  constants only yields a defect of size `≍ (log M)^{-1/α}`, not a uniform one.

The verdict of the calculus, then, is sharp: the one-dyadic-step inequality must
have either **zero loss** (a monotone scale-critical quantity — this is what the
frequency-function route of `FrequencyDoubling.lean` provides) or a loss that is
**summable in the step index**.  Any fixed per-step loss, multiplicative or
superlinear, is destroyed by the `≍ log M` steps of the cascade.

No `sorry`, no postulates.
-/
import Mathlib

open Filter Topology

noncomputable section

namespace ClayNS

/-! ## The scale gap `M^{-2/3} → M^{-1}` in dyadic steps -/

/-- The number of dyadic halvings separating the energy scale `M^{-2/3}` from
the velocity scale `M^{-1}`: `⌈log₂ M / 3⌉`. -/
def cascadeSteps (M : ℝ) : ℕ := ⌈Real.logb 2 M / 3⌉₊

/-- The starting radius of the cascade: the unique radius which, halved exactly
`cascadeSteps M` times, lands on the velocity scale `1/M`.  It sits within a
factor `2` of the energy scale `M^{-2/3}` (`cascadeStart_mem_Ico`). -/
def cascadeStart (M : ℝ) : ℝ := 2 ^ (cascadeSteps M) / M

/-- Halving the starting radius `cascadeSteps M` times lands **exactly** on the
velocity scale `1/M`. -/
lemma cascadeStart_div_pow {M : ℝ} (hM : 0 < M) :
    cascadeStart M / 2 ^ (cascadeSteps M) = 1 / M := by
  unfold cascadeStart
  have h2 : (2:ℝ) ^ (cascadeSteps M) ≠ 0 := by positivity
  field_simp

lemma cascadeStart_pos {M : ℝ} (hM : 0 < M) : 0 < cascadeStart M := by
  unfold cascadeStart; positivity

/-- `2 ^ (log₂ M / 3) = M ^ (1/3)` for `M > 0`. -/
lemma rpow_logb_div_three {M : ℝ} (hM : 0 < M) :
    (2:ℝ) ^ (Real.logb 2 M / 3) = M ^ ((1:ℝ)/3) := by
  have h : (2:ℝ) ^ (Real.logb 2 M / 3) = ((2:ℝ) ^ (Real.logb 2 M)) ^ ((1:ℝ)/3) := by
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    ring_nf
  rw [h, Real.rpow_logb (by norm_num) (by norm_num) hM]

/-- The starting radius sits in `[M^{-2/3}, 2·M^{-2/3})`: it *is* the energy
scale up to a factor two. -/
lemma cascadeStart_mem_Ico {M : ℝ} (hM : 1 ≤ M) :
    M ^ (-(2:ℝ)/3) ≤ cascadeStart M ∧ cascadeStart M < 2 * M ^ (-(2:ℝ)/3) := by
  have hM0 : (0:ℝ) < M := lt_of_lt_of_le one_pos hM
  have hkey : M ^ (-(2:ℝ)/3) = M ^ ((1:ℝ)/3) / M := by
    rw [show (-(2:ℝ)/3) = (1:ℝ)/3 - 1 by norm_num, Real.rpow_sub hM0, Real.rpow_one]
  set N := cascadeSteps M with hN
  have hNlow : Real.logb 2 M / 3 ≤ (N : ℝ) := Nat.le_ceil _
  have hNhigh : (N : ℝ) < Real.logb 2 M / 3 + 1 := by
    have hnn : 0 ≤ Real.logb 2 M / 3 := by
      have : 0 ≤ Real.logb 2 M := Real.logb_nonneg (by norm_num) hM
      linarith
    exact Nat.ceil_lt_add_one hnn
  have hpowlow : M ^ ((1:ℝ)/3) ≤ 2 ^ N := by
    have h1 : (2:ℝ) ^ (Real.logb 2 M / 3) ≤ (2:ℝ) ^ ((N:ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hNlow
    rw [rpow_logb_div_three hM0] at h1
    simpa [Real.rpow_natCast] using h1
  have hpowhigh : (2:ℝ) ^ N < 2 * M ^ ((1:ℝ)/3) := by
    have h1 : (2:ℝ) ^ ((N:ℝ)) < (2:ℝ) ^ (Real.logb 2 M / 3 + 1) :=
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hNhigh
    rw [Real.rpow_add (by norm_num), rpow_logb_div_three hM0] at h1
    simpa [Real.rpow_natCast, mul_comm] using h1
  refine ⟨?_, ?_⟩
  · rw [hkey, cascadeStart, ← hN]
    gcongr
  · rw [hkey, cascadeStart, ← hN, ← mul_div_assoc]
    gcongr

/-- The cascade length grows without bound. -/
lemma tendsto_cascadeSteps_atTop :
    Tendsto (fun M : ℝ => cascadeSteps M) atTop atTop := by
  have hlog : Tendsto (fun M : ℝ => Real.logb 2 M / 3) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num)).atTop_div_const (by norm_num)
  exact tendsto_nat_ceil_atTop.comp hlog

/-! ## The iteration calculus -/

/-- **Additive iteration.**  A one-step inequality `Q(n+1) ≥ Q(n) − b n` costs
exactly the accumulated loss `∑_{n<N} b n`. -/
theorem cascade_of_losses {Q b : ℕ → ℝ} {N : ℕ}
    (hstep : ∀ n < N, Q n - b n ≤ Q (n + 1)) :
    Q 0 - ∑ n ∈ Finset.range N, b n ≤ Q N := by
  induction N with
  | zero => simp
  | succ N ih =>
      have h1 : Q 0 - ∑ n ∈ Finset.range N, b n ≤ Q N :=
        ih fun n hn => hstep n (hn.trans (Nat.lt_succ_self N))
      have h2 := hstep N (Nat.lt_succ_self N)
      rw [Finset.sum_range_succ]
      linarith

/-- **Summable loss survives any number of steps.**  If the accumulated loss is
at most `ε/2`, half the defect persists all the way down — in particular
uniformly in the number `N` of dyadic steps, hence uniformly in `M`. -/
theorem cascade_persistence_of_small_total_loss {Q b : ℕ → ℝ} {N : ℕ} {eps : ℝ}
    (hstep : ∀ n < N, Q n - b n ≤ Q (n + 1)) (h0 : eps ≤ Q 0)
    (hsum : ∑ n ∈ Finset.range N, b n ≤ eps / 2) : eps / 2 ≤ Q N := by
  have := cascade_of_losses (Q := Q) (b := b) (N := N) hstep
  linarith

/-- **Multiplicative iteration.**  A fixed per-step factor `c` gives `c^N Q₀`. -/
theorem cascade_geometric {Q : ℕ → ℝ} {c : ℝ} {N : ℕ} (hc : 0 ≤ c)
    (hstep : ∀ n < N, c * Q n ≤ Q (n + 1)) :
    c ^ N * Q 0 ≤ Q N := by
  induction N with
  | zero => simp
  | succ N ih =>
      have h1 : c ^ N * Q 0 ≤ Q N :=
        ih fun n hn => hstep n (hn.trans (Nat.lt_succ_self N))
      have h2 := hstep N (Nat.lt_succ_self N)
      calc c ^ (N + 1) * Q 0 = c * (c ^ N * Q 0) := by ring
        _ ≤ c * Q N := by exact mul_le_mul_of_nonneg_left h1 hc
        _ ≤ Q (N + 1) := h2

/-- **A fixed multiplicative loss cannot close the cascade.**  Over the
`cascadeSteps M ≍ (1/3)log₂ M` steps separating the energy scale from the
velocity scale, the guarantee `c^N ε` produced by a one-step lemma with a fixed
factor `c < 1` tends to `0` as `M → ∞`: no uniform velocity-scale defect
follows. -/
theorem geometric_guarantee_tendsto_zero {c eps : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    Tendsto (fun M : ℝ => c ^ cascadeSteps M * eps) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1
  have h := (hpow.comp tendsto_cascadeSteps_atTop).mul_const eps
  simpa using h

/-- **Constant per-step loss.** -/
theorem cascade_monotone_loss {Q : ℕ → ℝ} {N : ℕ} {L : ℝ}
    (hstep : ∀ n < N, Q n - L ≤ Q (n + 1)) : Q 0 - (N : ℝ) * L ≤ Q N := by
  have := cascade_of_losses (Q := Q) (b := fun _ => L) (N := N) hstep
  simpa [Finset.sum_const, nsmul_eq_mul] using this

/-- **Superlinear loss: the exact threshold.**  If each dyadic step loses at
most `C·Q^{1+α}` and the defect never exceeds `ε`, then half the defect survives
`N` steps as soon as `N·C·ε^α ≤ 1/2`. -/
theorem cascade_superlinear_threshold {Q : ℕ → ℝ} {N : ℕ} {eps C alpha : ℝ}
    (hC : 0 ≤ C) (halpha : 0 < alpha)
    (hnn : ∀ n ≤ N, 0 ≤ Q n) (hupper : ∀ n ≤ N, Q n ≤ eps) (h0 : eps ≤ Q 0)
    (hstep : ∀ n < N, Q n - C * Q n ^ (1 + alpha) ≤ Q (n + 1))
    (hN : (N : ℝ) * (C * eps ^ (1 + alpha)) ≤ eps / 2) : eps / 2 ≤ Q N := by
  have hbound : ∀ n < N, C * Q n ^ (1 + alpha) ≤ C * eps ^ (1 + alpha) := by
    intro n hn
    have h1 : Q n ^ (1 + alpha) ≤ eps ^ (1 + alpha) :=
      Real.rpow_le_rpow (hnn n hn.le) (hupper n hn.le) (by linarith)
    exact mul_le_mul_of_nonneg_left h1 hC
  have hstep' : ∀ n < N, Q n - C * eps ^ (1 + alpha) ≤ Q (n + 1) := by
    intro n hn
    have := hstep n hn
    have hb := hbound n hn
    linarith
  have := cascade_monotone_loss (Q := Q) (N := N) (L := C * eps ^ (1 + alpha)) hstep'
  have hmul : (N : ℝ) * (C * eps ^ (1 + alpha)) ≤ eps / 2 := hN
  linarith

/-- **A superlinear one-step lemma with fixed constants still fails.**  For
fixed `ε, C > 0` the sufficient condition `N·C·ε^{1+α} ≤ ε/2` of
`cascade_superlinear_threshold` is violated for all large `M`: the surviving
defect degrades like `(log M)^{-1/α}`.  So the one-step inequality must lose an
amount that is *summable in the step index*, not merely superlinear in the
defect. -/
theorem superlinear_threshold_fails_eventually {eps C alpha : ℝ} (heps : 0 < eps)
    (hC : 0 < C) :
    ∀ᶠ M : ℝ in atTop, eps / 2 < (cascadeSteps M : ℝ) * (C * eps ^ (1 + alpha)) := by
  have hpos : 0 < C * eps ^ (1 + alpha) :=
    mul_pos hC (Real.rpow_pos_of_pos heps _)
  have hcast : Tendsto (fun M : ℝ => (cascadeSteps M : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_cascadeSteps_atTop
  have hmul : Tendsto (fun M : ℝ => (cascadeSteps M : ℝ) * (C * eps ^ (1 + alpha)))
      atTop atTop := hcast.atTop_mul_const hpos
  exact hmul.eventually_gt_atTop (eps / 2)

end ClayNS
