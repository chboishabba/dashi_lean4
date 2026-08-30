/-
# Zooming into the trajectory pane

`visualization/moonshine-trajectories.svg` draws, in its first pane, the curves

```
t ↦ T_j(1/2 + it) = ∑_{n ≤ K} e^{2πijn/24} n^{-1/2-it},   t : 0 → 30,  K = 500,
```

which spiral.  This file proves the structural facts that the zoomed picture
`visualization/moonshine-trajectories-zoom.svg` annotates:

* `cpow_neg_eq_polar` : the polar form `n^{-(σ+it)} = n^{-σ} e^{-i t log n}` of a single term;
* `norm_mtTerm`, `norm_mtTerm_antitone` : the `n`-th step of the partial-sum polygon has length
  `n^{-σ}` — at `σ = 1/2` this is `1/√n` — independent of the twist `j` and of `t`, and the
  steps shrink;
* `mtTerm_succ_eq` : consecutive steps differ by the rotation through `turn t n = t log((n+1)/n)`;
* `sum_turn` : those turning angles **telescope**, `∑_{n<K} turn t n = t log K`, so the polygon
  makes exactly `t log K / 2π` full turns — this is the spiral in the picture;
* `turn_antitone`, `sum_turn_tendsto_atTop` : the turning per step decreases while the total
  turning diverges, i.e. the spiral opens out and winds infinitely often;
* `hasDerivAt_mtPartial`, `norm_deriv_term` : the velocity of the plotted trajectory in `t`.
-/
import Mathlib
import RequestProject.MoonshineBridge

open Complex Finset

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MoonshineZoom

/-! ## The terms of the truncated series -/

/-- The `n`-th term of the `j`-th McKay–Thompson series in the Dirichlet grading,
`e^{2πijn/24} n^{-s}`. -/
noncomputable def mtTerm (j n : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j * n : ℕ) / 24) * (n : ℂ) ^ (-s)

/-- The truncated series `∑_{n = 1}^{K} e^{2πijn/24} n^{-s}` — the curve that the picture
draws as `t` runs along the critical line. -/
noncomputable def mtPartial (j K : ℕ) (s : ℂ) : ℂ := ∑ n ∈ Finset.Icc 1 K, mtTerm j n s

/-- At `j = 0` the truncated series is the truncated zeta function. -/
theorem mtPartial_zero (K : ℕ) (s : ℂ) : mtPartial 0 K s = MoonshineBridge.zetaPartialC K s := by
  simp [mtPartial, mtTerm, MoonshineBridge.zetaPartialC]

/-- **Polar form of a term.**  `n^{-(σ+it)} = n^{-σ} · e^{-i t log n}` for `n ≥ 1`: modulus
`n^{-σ}`, argument `−t log n`. -/
theorem cpow_neg_eq_polar {n : ℕ} (hn : 1 ≤ n) (sigma t : ℝ) :
    (n : ℂ) ^ (-((sigma : ℂ) + t * Complex.I))
      = ((n : ℝ) ^ (-sigma) : ℝ) * Complex.exp (-(t * Real.log n) * Complex.I) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  rw [Complex.cpow_def_of_ne_zero hn0, ← Complex.natCast_log, Real.rpow_def_of_pos hnpos,
    Complex.ofReal_exp, ← Complex.exp_add]
  push_cast
  ring_nf

/-- **The step lengths of the partial-sum polygon.**  `‖e^{2πijn/24} n^{-s}‖ = n^{-Re s}`,
independent of `j` and of `t`: at `σ = 1/2` the `n`-th step of the spiral has length
`1/√n`. -/
theorem norm_mtTerm {n : ℕ} (hn : 1 ≤ n) (j : ℕ) (s : ℂ) :
    ‖mtTerm j n s‖ = (n : ℝ) ^ (-s.re) := by
  rw [mtTerm, norm_mul, Complex.norm_exp, Complex.norm_natCast_cpow_of_pos hn]
  simp

/-- The step lengths decrease (for `σ ≥ 0`). -/
theorem norm_mtTerm_antitone {n : ℕ} (hn : 1 ≤ n) (j : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖mtTerm j (n + 1) s‖ ≤ ‖mtTerm j n s‖ := by
  rw [norm_mtTerm (by omega) j s, norm_mtTerm hn j s]
  have h1 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : ((n : ℝ)) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
  exact Real.rpow_le_rpow_of_nonpos h1 h2 (by linarith)

/-! ## The turning of the polygon -/

/-- The angle by which the partial-sum polygon turns at its `n`-th vertex, `t·log((n+1)/n)`. -/
noncomputable def turn (t : ℝ) (n : ℕ) : ℝ := t * Real.log ((n + 1 : ℝ) / n)

/-- **Consecutive steps differ by a rotation through `turn t n`.**  Writing the terms in polar
form, the `(n+1)`-st term is the `n`-th one scaled by `(n/(n+1))^σ` and rotated by
`−t·log((n+1)/n)`. -/
theorem mtTerm_succ_eq {n : ℕ} (hn : 1 ≤ n) (sigma t : ℝ) :
    ((n + 1 : ℕ) : ℂ) ^ (-((sigma : ℂ) + t * Complex.I))
      = (((n : ℝ) / (n + 1)) ^ sigma : ℝ)
        * Complex.exp (-(turn t n) * Complex.I)
        * (n : ℂ) ^ (-((sigma : ℂ) + t * Complex.I)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [cpow_neg_eq_polar (by omega : 1 ≤ n + 1) sigma t, cpow_neg_eq_polar hn sigma t, turn,
    Real.log_div (by positivity) (by positivity)]
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have hr : (((n : ℝ) + 1) ^ (-sigma) : ℝ)
      = (((n : ℝ) / ((n : ℝ) + 1)) ^ sigma : ℝ) * ((n : ℝ) ^ (-sigma)) := by
    rw [Real.div_rpow (le_of_lt hnpos) (by positivity), Real.rpow_neg (by positivity),
      Real.rpow_neg (by positivity)]
    field_simp
  have key : ∀ A B u v : ℂ,
      A * Complex.exp u * (B * Complex.exp v) = A * B * Complex.exp (u + v) := by
    intro A B u v
    rw [Complex.exp_add]
    ring
  rw [hr]
  push_cast
  rw [key]
  ring_nf

/-- **The turning angles telescope.**  The total turning of the polygon `∑_{n ≤ K} n^{-σ-it}`
from its first step to its last is exactly `t·log K`; divided by `2π` this is the number of
full turns of the spiral. -/
theorem sum_turn (t : ℝ) (K : ℕ) (hK : 1 ≤ K) :
    ∑ n ∈ Finset.Ico 1 K, turn t n = t * Real.log K := by
  induction K with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hK with h | h
    · simp [← h]
    · have hm : 1 ≤ m := by omega
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
      rw [Finset.sum_Ico_succ_top hm, ih hm, turn,
        Real.log_div (by positivity) (by positivity)]
      push_cast
      ring_nf

/-- The turning angles decrease: the spiral opens out. -/
theorem turn_antitone {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) : turn t (n + 1) ≤ turn t n := by
  have hm0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine mul_le_mul_of_nonneg_left ?_ ht
  apply Real.log_le_log (by push_cast; positivity)
  rw [div_le_div_iff₀ (by push_cast; positivity) hm0]
  push_cast
  nlinarith

/-- **The spiral winds arbitrarily often**: the total turning `t·log K` of the polygon tends to
`∞` with the truncation length, for every `t > 0`. -/
theorem sum_turn_tendsto_atTop {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun K : ℕ => ∑ n ∈ Finset.Ico 1 K, turn t n) Filter.atTop Filter.atTop := by
  have h : (fun K : ℕ => ∑ n ∈ Finset.Ico 1 K, turn t n)
      =ᶠ[Filter.atTop] (fun K : ℕ => t * Real.log K) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with K hK using sum_turn t K hK
  refine Filter.Tendsto.congr' h.symm ?_
  exact Filter.Tendsto.const_mul_atTop ht
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-! ## The velocity of the trajectory -/

/-- Each term of the truncated series moves, as `t` increases along the vertical line
`s = σ + it`, with velocity `(−i log n)` times itself. -/
theorem hasDerivAt_term (j : ℕ) {n : ℕ} (hn : 1 ≤ n) (sigma t : ℝ) :
    HasDerivAt (fun u : ℝ => mtTerm j n ((sigma : ℂ) + u * Complex.I))
      ((-(Real.log n : ℂ) * Complex.I) * mtTerm j n ((sigma : ℂ) + t * Complex.I)) t := by
  have hfun : (fun u : ℝ => mtTerm j n ((sigma : ℂ) + u * Complex.I))
      = fun u : ℝ => (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j * n : ℕ) / 24)
          * ((n : ℝ) ^ (-sigma) : ℝ)) * Complex.exp ((-(Real.log n : ℂ) * Complex.I) * u) := by
    funext u
    rw [mtTerm, cpow_neg_eq_polar hn sigma u]
    push_cast
    ring_nf
  rw [hfun]
  have h1 : HasDerivAt (fun u : ℝ => (-(Real.log n : ℂ) * Complex.I) * (u : ℂ))
      (-(Real.log n : ℂ) * Complex.I) t := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-(Real.log n : ℂ) * Complex.I)
  have h2 := (h1.cexp).const_mul (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j * n : ℕ) / 24)
    * ((n : ℝ) ^ (-sigma) : ℝ))
  convert h2 using 1
  rw [mtTerm, cpow_neg_eq_polar hn sigma t]
  push_cast
  ring_nf

/-- **The velocity of the plotted curve.**  Along the vertical line `s = σ + it` the truncated
series moves with velocity `∑_{n ≤ K} (−i log n)·e^{2πijn/24} n^{-s}`. -/
theorem hasDerivAt_mtPartial (j K : ℕ) (sigma t : ℝ) :
    HasDerivAt (fun u : ℝ => mtPartial j K ((sigma : ℂ) + u * Complex.I))
      (∑ n ∈ Finset.Icc 1 K, (-(Real.log n : ℂ) * Complex.I) * mtTerm j n
        ((sigma : ℂ) + t * Complex.I)) t := by
  simp only [mtPartial]
  have hswap : (fun u : ℝ => ∑ n ∈ Finset.Icc 1 K, mtTerm j n ((sigma : ℂ) + u * Complex.I))
      = ∑ n ∈ Finset.Icc 1 K, (fun u : ℝ => mtTerm j n ((sigma : ℂ) + u * Complex.I)) := by
    funext u
    simp [Finset.sum_apply]
  rw [hswap]
  exact HasDerivAt.sum fun n hn => hasDerivAt_term j (Finset.mem_Icc.mp hn).1 sigma t

/-- The speed contributed by a single term is `log n · n^{-σ}`: the later, shorter steps of the
polygon sweep the fastest. -/
theorem norm_deriv_term {n : ℕ} (hn : 1 ≤ n) (j : ℕ) (s : ℂ) :
    ‖(-(Real.log n : ℂ) * Complex.I) * mtTerm j n s‖ = Real.log n * (n : ℝ) ^ (-s.re) := by
  have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  rw [norm_mul, norm_mtTerm hn j s, norm_mul, norm_neg, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]

end MoonshineZoom
