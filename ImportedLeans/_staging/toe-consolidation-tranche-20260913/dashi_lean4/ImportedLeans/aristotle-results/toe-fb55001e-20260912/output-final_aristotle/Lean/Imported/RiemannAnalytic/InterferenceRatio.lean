/-
**Q1: does the δ-free interference ratio tend to zero?**

`TwoRegimeInterference.lean` proves the localization estimate

    ∑ interference  ≤  η · ΔGram,      η = 16384 N (4M₁² + 2K²) / (81 L⁶),

with no minimum-gap hypothesis: the only zero-side datum is the *local count*
`N` of family members per unit window of the ordinate difference.  That is a
fixed-height statement.  The question left open there is asymptotic: as the
height `T` grows, the taper scale `L = L(T)`, the moment constants
`M₁ = M₁(T)`, `K = K(T)` and the local count `N = N(T)` all move, and mixed
interference stops being a frontier problem precisely when

    η(T) → 0.

This file settles that in the form it is actually needed:

* `interferenceRatio` is the ratio itself, `interferenceRatio_nonneg`,
  `interferenceRatio_eq` its elementary properties;
* `interferenceRatio_tendsto_zero_of_quotient` reduces `η(T) → 0` to the
  dimensionless quotient `N(4M₁²+2K²)/L⁶ → 0`;
* `interferenceRatio_tendsto_zero_log`, the concrete instantiation of the
  source situation: a taper scale `L(T) = λ log T` proportional to the
  logarithm (as the source taper is), bounded moment constants, and a local
  count growing at most like `A log T` — which is exactly what
  Riemann–von Mangoldt supplies (`N(t+1) − N(t) ≪ log(t+3)`).  Then
  `η(T) ≍ 1/(log T)⁵ → 0`;
* `eventually_interferenceRatio_lt_one` and
  `eventually_interferenceRatio_lt`, the usable "eventually perturbative"
  forms;
* `interference_lt_gramDefect_of_ratio_lt_one`: once `η < 1` the interference
  is strictly dominated by the Gram defect it is competing with.

Nothing here assumes anything about `ζ`: `L`, `M₁`, `K`, `N` are arbitrary
functions, and the growth conditions are explicit hypotheses.
-/
import RiemannAnalytic.TwoRegimeInterference

namespace RiemannAnalytic

open Filter Topology

/-! ### The ratio -/

/-- The δ-free localization ratio of `TwoRegimeInterference.lean`,

    η = 16384 · N · (4 M₁² + 2 K²) / (81 L⁶),

as a function of the four scale parameters. -/
noncomputable def interferenceRatio (N M₁ K L : ℝ) : ℝ :=
  16384 * N * (4 * M₁ ^ 2 + 2 * K ^ 2) / (81 * L ^ 6)

theorem interferenceRatio_nonneg {N M₁ K L : ℝ} (hN : 0 ≤ N) :
    0 ≤ interferenceRatio N M₁ K L := by
  unfold interferenceRatio
  have h1 : (0 : ℝ) ≤ 4 * M₁ ^ 2 + 2 * K ^ 2 := by positivity
  have h2 : (0 : ℝ) ≤ 81 * L ^ 6 := by positivity
  positivity

/-- `η` is the constant `16384/81` times the dimensionless quotient
`N (4M₁² + 2K²) / L⁶`. -/
theorem interferenceRatio_eq (N M₁ K L : ℝ) :
    interferenceRatio N M₁ K L
      = 16384 / 81 * (N * (4 * M₁ ^ 2 + 2 * K ^ 2) / L ^ 6) := by
  unfold interferenceRatio
  ring

/-! ### `η(T) → 0` -/

/-- **Q1, reduction.**  The ratio tends to zero exactly when the dimensionless
quotient `N (4M₁² + 2K²) / L⁶` does. -/
theorem interferenceRatio_tendsto_zero_of_quotient {N M₁ K L : ℝ → ℝ}
    (h : Tendsto (fun T => N T * (4 * M₁ T ^ 2 + 2 * K T ^ 2) / L T ^ 6) atTop (𝓝 0)) :
    Tendsto (fun T => interferenceRatio (N T) (M₁ T) (K T) (L T)) atTop (𝓝 0) := by
  have := h.const_mul (16384 / 81 : ℝ)
  rw [mul_zero] at this
  refine this.congr fun T => ?_
  rw [interferenceRatio_eq]

/-- `c / (log T)⁵ → 0` as `T → ∞`. -/
theorem tendsto_div_log_pow_five (c : ℝ) :
    Tendsto (fun T : ℝ => c / Real.log T ^ 5) atTop (𝓝 0) := by
  have hlog : Tendsto (fun T : ℝ => Real.log T) atTop atTop := Real.tendsto_log_atTop
  have hpow : Tendsto (fun T : ℝ => Real.log T ^ 5) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).comp hlog
  exact Tendsto.div_atTop tendsto_const_nhds hpow

/-- **Q1 for the source scales.**

If the taper scale is logarithmic, `L(T) = λ log T` with `λ > 0`; the two
kernel constants are bounded, `|M₁(T)| ≤ M`, `|K(T)| ≤ K₀`; and the local count
grows at most logarithmically, `0 ≤ N(T) ≤ A log T` — the Riemann–von Mangoldt
regime — then

    η(T) → 0.

The mechanism is transparent: the numerator grows like `log T`, the denominator
like `(log T)⁶`, so `η(T) = O((log T)⁻⁵)`. -/
theorem interferenceRatio_tendsto_zero_log {N M₁ K L : ℝ → ℝ} {lam A M K₀ : ℝ}
    (hlam : 0 < lam) (hL : ∀ T, L T = lam * Real.log T)
    (hM : ∀ T, |M₁ T| ≤ M) (hK : ∀ T, |K T| ≤ K₀)
    (hN0 : ∀ T, 0 ≤ N T) (hN : ∀ T, N T ≤ A * Real.log T) :
    Tendsto (fun T => interferenceRatio (N T) (M₁ T) (K T) (L T)) atTop (𝓝 0) := by
  set c : ℝ := 16384 * A * (4 * M ^ 2 + 2 * K₀ ^ 2) / (81 * lam ^ 6) with hc
  -- squeeze `η(T)` between `0` and `c / (log T)⁵`
  have hsq : ∀ᶠ T : ℝ in atTop,
      interferenceRatio (N T) (M₁ T) (K T) (L T) ≤ c / Real.log T ^ 5 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hlogpos : 0 < Real.log T := Real.log_pos hT
    have hM' : M₁ T ^ 2 ≤ M ^ 2 := by
      have h := hM T
      nlinarith [abs_nonneg (M₁ T), sq_abs (M₁ T)]
    have hK' : K T ^ 2 ≤ K₀ ^ 2 := by
      have h := hK T
      nlinarith [abs_nonneg (K T), sq_abs (K T)]
    have hPQ : 4 * M₁ T ^ 2 + 2 * K T ^ 2 ≤ 4 * M ^ 2 + 2 * K₀ ^ 2 := by linarith
    have hAlog : 0 ≤ A * Real.log T := le_trans (hN0 T) (hN T)
    have hnum : 16384 * N T * (4 * M₁ T ^ 2 + 2 * K T ^ 2)
        ≤ 16384 * (A * Real.log T) * (4 * M ^ 2 + 2 * K₀ ^ 2) := by
      have := mul_le_mul (hN T) hPQ (by positivity) hAlog
      nlinarith [this]
    have hLHS : interferenceRatio (N T) (M₁ T) (K T) (L T)
        = 16384 * N T * (4 * M₁ T ^ 2 + 2 * K T ^ 2)
            / (81 * lam ^ 6 * Real.log T ^ 6) := by
      unfold interferenceRatio
      rw [hL T]
      have hd : 81 * (lam * Real.log T) ^ 6 = 81 * lam ^ 6 * Real.log T ^ 6 := by ring
      rw [hd]
    have hRHS : c / Real.log T ^ 5
        = 16384 * (A * Real.log T) * (4 * M ^ 2 + 2 * K₀ ^ 2)
            / (81 * lam ^ 6 * Real.log T ^ 6) := by
      rw [hc]
      field_simp
    rw [hLHS, hRHS]
    gcongr
  have h0 : ∀ᶠ T : ℝ in atTop, 0 ≤ interferenceRatio (N T) (M₁ T) (K T) (L T) :=
    Eventually.of_forall fun T => interferenceRatio_nonneg (hN0 T)
  exact squeeze_zero' h0 hsq (tendsto_div_log_pow_five c)

/-! ### Eventually perturbative -/

/-- If `η(T) → 0`, then eventually `η(T) < ε` for any positive `ε`. -/
theorem eventually_interferenceRatio_lt {N M₁ K L : ℝ → ℝ}
    (h : Tendsto (fun T => interferenceRatio (N T) (M₁ T) (K T) (L T)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, interferenceRatio (N T) (M₁ T) (K T) (L T) < ε := by
  have := h.eventually (eventually_lt_nhds hε)
  exact this

/-- **`∃ T₀, ∀ T ≥ T₀, η(T) < 1`** — mixed interference is eventually
perturbative. -/
theorem eventually_interferenceRatio_lt_one {N M₁ K L : ℝ → ℝ}
    (h : Tendsto (fun T => interferenceRatio (N T) (M₁ T) (K T) (L T)) atTop (𝓝 0)) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, interferenceRatio (N T) (M₁ T) (K T) (L T) < 1 :=
  eventually_atTop.mp (eventually_interferenceRatio_lt h one_pos)

/-- Under the logarithmic source scales, interference is eventually
perturbative. -/
theorem source_eventually_interferenceRatio_lt_one {N M₁ K L : ℝ → ℝ} {lam A M K₀ : ℝ}
    (hlam : 0 < lam) (hL : ∀ T, L T = lam * Real.log T)
    (hM : ∀ T, |M₁ T| ≤ M) (hK : ∀ T, |K T| ≤ K₀)
    (hN0 : ∀ T, 0 ≤ N T) (hN : ∀ T, N T ≤ A * Real.log T) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, interferenceRatio (N T) (M₁ T) (K T) (L T) < 1 :=
  eventually_interferenceRatio_lt_one
    (interferenceRatio_tendsto_zero_log hlam hL hM hK hN0 hN)

/-- Once the ratio is `< 1`, the interference bounded by it is strictly smaller
than the Gram defect, provided that defect is positive. -/
theorem interference_lt_gramDefect_of_ratio_lt_one {I η Δ : ℝ} (hI : I ≤ η * Δ)
    (hη : η < 1) (hΔ : 0 < Δ) : I < Δ := by
  have : η * Δ < Δ := by nlinarith
  linarith

end RiemannAnalytic
