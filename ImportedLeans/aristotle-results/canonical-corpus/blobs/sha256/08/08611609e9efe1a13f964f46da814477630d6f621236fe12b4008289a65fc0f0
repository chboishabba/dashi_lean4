/-
**Purify before taking the mean square: the finite shift projector.**

The methodological principle imported here is the one the modular-source
programme uses: do not estimate a generic object and hope for cancellation —
apply first an explicit finite operator that *annihilates* the unwanted
component, and only then take the mean square.

On the Dirichlet-polynomial side the admissible operators are the finite shift
combinations

    `(P D)(t) = ∑_{j < r} c_j · D(t + s_j)`,

because a shift acts diagonally on frequencies: `D(t + s)` multiplies the
coefficient `a_n` by the symbol `n^{-is}`.  This file proves that exactly, and
computes the resulting diagonal.

* `shiftProjected_dirichletPoly` — `P D` is again a Dirichlet polynomial, with
  coefficients `a_n · P(n^{-is})`, `P(z) = ∑_j c_j z^{s_j}` realised as
  `shiftMultiplier`.
* `shiftMultiplier_zeroFreq` / `shiftMultiplier_zeroFreq_eq_zero` — the value at
  the zero frequency (i.e. at `n = 1`) is exactly `∑_j c_j`.  So the
  normalisation `P(1) = 0` annihilates the zero-frequency mode **exactly**, with
  no estimate involved.
* `norm_shiftSymbol_sub_one_eq` — the exact symbol modulus
  `‖n^{-is} − 1‖ = 2|sin(s log n / 2)|`, and `norm_shiftSymbol_sub_one_le`, its
  linearisation `≤ |s log n|`.
* `norm_shiftMultiplier_le_of_annihilating` — hence any annihilating projector
  damps the frequency `λ` by at least `(∑_j ‖c_j‖|s_j|)·|λ|`.
* `dirichletPoly_firstDifference` and `diff_diagonalMass_le` — for the simplest
  projector `D(t+s) − D(t)` the transformed diagonal obeys

      `∑_n ‖a_n(n^{-is} − 1)‖² ≤ (|s| log N)² ∑_n ‖a_n‖²`,

  with the `n = 1` term removed exactly (`diffCoeff_one`); and
  `projected_secondMoment_le` feeds this into the exact short-window expansion
  of `ShortIntervalMeanValue.lean`.

**And the ledger entry that this produces, which is negative at the source
scale.**  `norm_shiftSymbol_sub_one_eq_two_of_pi` shows the damping factor is
*not* small — it equals `2` — at every frequency with `s·λ = π`; and
`source_gain_factor_eq` computes the damping exponent at the source parameters:
with grid spacing `s = 2π/L` and polynomial length `log N = cL`, the factor
`(|s| log N)² = (2πc)²` is a **constant, independent of `L`**.  So a fixed
finite shift projector at the source grid spacing buys no power of `L`; it buys
a genuine gain exactly when `|s| log N → 0` (`gain_tendsto_zero_of_short`), i.e.
only for polynomial lengths `log N = o(L)`.

Nothing here refers to `ζ`: `a` is an arbitrary finite coefficient sequence, and
no arithmetic input is assumed anywhere.
-/
import RiemannAnalytic.ShortIntervalMeanValue

namespace RiemannAnalytic

open Complex Finset intervalIntegral MeasureTheory

/-! ### The shift symbol -/

/-- The symbol by which the shift `t ↦ t + s` multiplies the frequency `λ`
component: `e^{-iλs}`; at `λ = log n` this is `n^{-is}`. -/
noncomputable def shiftSymbol (s lam : ℝ) : ℂ :=
  Complex.exp (-(Complex.I * (lam : ℂ) * (s : ℂ)))

@[simp] theorem shiftSymbol_zero_freq (s : ℝ) : shiftSymbol s 0 = 1 := by
  simp [shiftSymbol]

theorem norm_shiftSymbol (s lam : ℝ) : ‖shiftSymbol s lam‖ = 1 := by
  unfold shiftSymbol
  rw [Complex.norm_exp]
  simp

/-- **The exact symbol defect**: `‖e^{-iλs} − 1‖ = 2|sin(λs/2)|`. -/
theorem norm_shiftSymbol_sub_one_eq (s lam : ℝ) :
    ‖shiftSymbol s lam - 1‖ = 2 * |Real.sin (lam * s / 2)| := by
  have hrw : shiftSymbol s lam = Complex.exp (((-(lam * s) : ℝ) : ℂ) * Complex.I) := by
    unfold shiftSymbol
    congr 1
    push_cast
    ring
  set x : ℝ := -(lam * s) with hx
  rw [hrw]
  have h1 : Complex.exp ((x : ℂ) * Complex.I) - 1 = ⟨Real.cos x - 1, Real.sin x⟩ := by
    rw [Complex.exp_mul_I]
    simp [Complex.ext_iff, Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  rw [h1, Complex.norm_def, Complex.normSq_mk]
  have h := Real.cos_two_mul' (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  have hc : Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  have h2 : (Real.cos x - 1) * (Real.cos x - 1) + Real.sin x * Real.sin x
      = 4 * Real.sin (x / 2) ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x, hc]
  have habs : |Real.sin (x / 2)| = |Real.sin (lam * s / 2)| := by
    rw [hx, show -(lam * s) / 2 = -(lam * s / 2) by ring, Real.sin_neg, abs_neg]
  rw [h2, show (4 : ℝ) * Real.sin (x / 2) ^ 2 = (2 * |Real.sin (x / 2)|) ^ 2 by
      rw [mul_pow, sq_abs]; ring, Real.sqrt_sq (by positivity), habs]

/-- The linearised symbol defect: `‖e^{-iλs} − 1‖ ≤ |λs|`. -/
theorem norm_shiftSymbol_sub_one_le (s lam : ℝ) :
    ‖shiftSymbol s lam - 1‖ ≤ |lam * s| := by
  rw [norm_shiftSymbol_sub_one_eq]
  have hsin : |Real.sin (lam * s / 2)| ≤ |lam * s / 2| := Real.abs_sin_le_abs
  have : |lam * s / 2| = |lam * s| / 2 := by
    rw [abs_div]
    simp
  linarith [hsin, this ▸ hsin]

/-- **No damping at the critical frequency.**  The projector's damping factor is
`2`, not small, at every frequency with `λs = π`. -/
theorem norm_shiftSymbol_sub_one_eq_two_of_pi {s lam : ℝ} (h : lam * s = Real.pi) :
    ‖shiftSymbol s lam - 1‖ = 2 := by
  rw [norm_shiftSymbol_sub_one_eq, h]
  rw [Real.sin_pi_div_two]
  norm_num

/-! ### The general finite shift projector -/

/-- The multiplier `P(n^{-i·}) = ∑_{j<r} c_j e^{-iλ s_j}` attached to the finite
shift combination with coefficients `c` and shifts `s`. -/
noncomputable def shiftMultiplier (c : ℕ → ℂ) (sh : ℕ → ℝ) (r : ℕ) (lam : ℝ) : ℂ :=
  ∑ j ∈ Finset.range r, c j * shiftSymbol (sh j) lam

/-- The finite shift combination `∑_{j<r} c_j D(· + s_j)`. -/
noncomputable def shiftProjected (c : ℕ → ℂ) (sh : ℕ → ℝ) (r : ℕ) (D : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range r, c j * D (t + sh j)

/-- **The projector acts diagonally on frequencies.**  A finite shift
combination of a Dirichlet polynomial is again a Dirichlet polynomial, with each
coefficient multiplied by the symbol value `P(n^{-i·})`. -/
theorem shiftProjected_dirichletPoly (c : ℕ → ℂ) (sh : ℕ → ℝ) (r : ℕ) (a : ℕ → ℂ) (N : ℕ)
    (t : ℝ) :
    shiftProjected c sh r (dirichletPoly a N) t
      = dirichletPoly (fun n => a n * shiftMultiplier c sh r (Real.log n)) N t := by
  unfold shiftProjected dirichletPoly shiftMultiplier
  have hexp : ∀ j n : ℕ, Complex.exp (-(Complex.I * (Real.log n : ℂ) * ((t + sh j : ℝ) : ℂ)))
      = shiftSymbol (sh j) (Real.log n)
        * Complex.exp (-(Complex.I * (Real.log n : ℂ) * (t : ℂ))) := by
    intro j n
    unfold shiftSymbol
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc ∑ j ∈ Finset.range r, c j
        * ∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(Complex.I * (Real.log n : ℂ)
            * ((t + sh j : ℝ) : ℂ)))
      = ∑ j ∈ Finset.range r, ∑ n ∈ Finset.Icc 1 N,
          c j * shiftSymbol (sh j) (Real.log n)
            * (a n * Complex.exp (-(Complex.I * (Real.log n : ℂ) * (t : ℂ)))) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [hexp j n]
        ring
    _ = ∑ n ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range r,
          c j * shiftSymbol (sh j) (Real.log n)
            * (a n * Complex.exp (-(Complex.I * (Real.log n : ℂ) * (t : ℂ)))) :=
        Finset.sum_comm
    _ = ∑ n ∈ Finset.Icc 1 N,
          a n * (∑ j ∈ Finset.range r, c j * shiftSymbol (sh j) (Real.log n))
            * Complex.exp (-(Complex.I * (Real.log n : ℂ) * (t : ℂ))) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [← Finset.sum_mul]
        ring

/-- The value of the multiplier at the zero frequency — that is, at `n = 1`. -/
theorem shiftMultiplier_zeroFreq (c : ℕ → ℂ) (sh : ℕ → ℝ) (r : ℕ) :
    shiftMultiplier c sh r 0 = ∑ j ∈ Finset.range r, c j := by
  unfold shiftMultiplier
  simp

/-- **`P(1) = 0` annihilates the zero-frequency mode exactly.**  No estimate is
involved: the `n = 1` coefficient of the projected polynomial is `0`. -/
theorem shiftMultiplier_zeroFreq_eq_zero {c : ℕ → ℂ} {sh : ℕ → ℝ} {r : ℕ}
    (hc : ∑ j ∈ Finset.range r, c j = 0) : shiftMultiplier c sh r 0 = 0 := by
  rw [shiftMultiplier_zeroFreq, hc]

/-- **An annihilating projector damps every low frequency linearly.**  If
`∑_j c_j = 0` then

    `‖P(λ)‖ ≤ (∑_j ‖c_j‖ |s_j|) · |λ|`. -/
theorem norm_shiftMultiplier_le_of_annihilating {c : ℕ → ℂ} {sh : ℕ → ℝ} {r : ℕ}
    (hc : ∑ j ∈ Finset.range r, c j = 0) (lam : ℝ) :
    ‖shiftMultiplier c sh r lam‖ ≤ (∑ j ∈ Finset.range r, ‖c j‖ * |sh j|) * |lam| := by
  have hsplit : shiftMultiplier c sh r lam
      = ∑ j ∈ Finset.range r, c j * (shiftSymbol (sh j) lam - 1) := by
    unfold shiftMultiplier
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.range r) =>
      (by ring : c j * (shiftSymbol (sh j) lam - 1) = c j * shiftSymbol (sh j) lam - c j)]
    rw [Finset.sum_sub_distrib, hc, sub_zero]
  rw [hsplit]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [norm_mul]
  have h1 : ‖shiftSymbol (sh j) lam - 1‖ ≤ |lam| * |sh j| := by
    refine le_trans (norm_shiftSymbol_sub_one_le (sh j) lam) (le_of_eq ?_)
    rw [abs_mul]
  calc ‖c j‖ * ‖shiftSymbol (sh j) lam - 1‖
      ≤ ‖c j‖ * (|lam| * |sh j|) := by
        exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖c j‖ * |sh j| * |lam| := by ring

/-! ### The first difference, and the diagonal it produces -/

/-- The coefficients of the first-difference projector `D(·+s) − D(·)`. -/
noncomputable def diffCoeff (a : ℕ → ℂ) (s : ℝ) (n : ℕ) : ℂ :=
  a n * (shiftSymbol s (Real.log n) - 1)

/-- The `n = 1` coefficient is annihilated exactly. -/
@[simp] theorem diffCoeff_one (a : ℕ → ℂ) (s : ℝ) : diffCoeff a s 1 = 0 := by
  simp [diffCoeff]

/-- **The first difference of a Dirichlet polynomial** is the Dirichlet
polynomial of the differenced coefficients. -/
theorem dirichletPoly_firstDifference (a : ℕ → ℂ) (N : ℕ) (s t : ℝ) :
    dirichletPoly a N (t + s) - dirichletPoly a N t
      = dirichletPoly (diffCoeff a s) N t := by
  unfold dirichletPoly diffCoeff
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hexp : Complex.exp (-(Complex.I * (Real.log n : ℂ) * ((t + s : ℝ) : ℂ)))
      = shiftSymbol s (Real.log n)
        * Complex.exp (-(Complex.I * (Real.log n : ℂ) * (t : ℂ))) := by
    unfold shiftSymbol
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- The diagonal mass of a coefficient sequence: `∑_{1 ≤ n ≤ N} |a_n|²`. -/
noncomputable def diagonalMass (a : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2

theorem diagonalMass_nonneg (a : ℕ → ℂ) (N : ℕ) : 0 ≤ diagonalMass a N :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- **The transformed diagonal.**  The first-difference projector damps the
diagonal of the second moment by the factor `(|s| log N)²`:

    `∑_{n ≤ N} |a_n (n^{-is} − 1)|² ≤ (|s| log N)² ∑_{n ≤ N} |a_n|²`,

and the `n = 1` term is removed outright. -/
theorem diff_diagonalMass_le (a : ℕ → ℂ) (N : ℕ) (s : ℝ) :
    diagonalMass (diffCoeff a s) N ≤ (|s| * Real.log N) ^ 2 * diagonalMass a N := by
  unfold diagonalMass
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Finset.mem_Icc] at hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
  have hnN : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn.2
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlogN : Real.log n ≤ Real.log N := Real.log_le_log (by linarith) hnN
  have hsym : ‖shiftSymbol s (Real.log n) - 1‖ ≤ |s| * Real.log N := by
    refine le_trans (norm_shiftSymbol_sub_one_le s (Real.log n)) ?_
    rw [abs_mul, abs_of_nonneg hlog0]
    have : Real.log n * |s| ≤ Real.log N * |s| := by
      exact mul_le_mul_of_nonneg_right hlogN (abs_nonneg s)
    linarith [this]
  have hsym0 : 0 ≤ ‖shiftSymbol s (Real.log n) - 1‖ := norm_nonneg _
  have hsq : ‖shiftSymbol s (Real.log n) - 1‖ ^ 2 ≤ (|s| * Real.log N) ^ 2 := by
    nlinarith
  calc ‖diffCoeff a s n‖ ^ 2
      = ‖a n‖ ^ 2 * ‖shiftSymbol s (Real.log n) - 1‖ ^ 2 := by
        unfold diffCoeff
        rw [norm_mul, mul_pow]
    _ ≤ ‖a n‖ ^ 2 * (|s| * Real.log N) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (|s| * Real.log N) ^ 2 * ‖a n‖ ^ 2 := by ring

/-- **The projected short-window second moment.**  Combining the exact expansion
of `ShortIntervalMeanValue.lean` with the damped diagonal: the diagonal of the
*projected* polynomial costs `H (|s| log N)² ∑|a_n|²` instead of `H ∑|a_n|²`,
while the off-diagonal is the classical one for the projected coefficients. -/
theorem projected_secondMoment_le (a : ℕ → ℂ) (N : ℕ) {H : ℝ} (hH : 0 ≤ H) (s : ℝ) :
    (∫ t in (0 : ℝ)..H, ‖dirichletPoly a N (t + s) - dirichletPoly a N t‖ ^ 2)
      ≤ H * ((|s| * Real.log N) ^ 2 * diagonalMass a N)
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * ‖diffCoeff a s m‖ * ‖diffCoeff a s n‖ / |Real.log n - Real.log m| := by
  have hcongr : (∫ t in (0 : ℝ)..H, ‖dirichletPoly a N (t + s) - dirichletPoly a N t‖ ^ 2)
      = ∫ t in (0 : ℝ)..H, ‖dirichletPoly (diffCoeff a s) N t‖ ^ 2 := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [dirichletPoly_firstDifference]
  rw [hcongr]
  refine le_trans (dirichletPoly_secondMoment_le (diffCoeff a s) N hH) ?_
  have hdiag : H * ∑ n ∈ Finset.Icc 1 N, ‖diffCoeff a s n‖ ^ 2
      ≤ H * ((|s| * Real.log N) ^ 2 * diagonalMass a N) := by
    have := diff_diagonalMass_le a N s
    unfold diagonalMass at this
    exact mul_le_mul_of_nonneg_left this hH
  linarith

/-! ### The resource ledger for the projector -/

/-- **The ledger entry at the source parameters.**  With grid spacing
`s = 2π/L` and Dirichlet length `log N = cL`, the damping factor produced by one
first difference is `(2πc)²` — a constant, *independent of `L`*.  A fixed finite
shift projector at the source grid spacing therefore buys no power of `L`. -/
theorem source_gain_factor_eq {L c : ℝ} (hL : 0 < L) {N : ℕ}
    (hlog : Real.log N = c * L) :
    (|2 * Real.pi / L| * Real.log N) ^ 2 = (2 * Real.pi * c) ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [hlog, abs_of_pos (by positivity)]
  field_simp

/-- **When the projector does gain.**  The damping factor tends to `0` exactly
along parameter families whose product `|s| log N` tends to `0`, i.e. for
polynomial lengths short compared with the reciprocal grid spacing. -/
theorem gain_tendsto_zero_of_short {ι : Type*} {l : Filter ι} {s : ι → ℝ} {lN : ι → ℝ}
    (h : Filter.Tendsto (fun i => |s i| * lN i) l (nhds 0)) :
    Filter.Tendsto (fun i => (|s i| * lN i) ^ 2) l (nhds 0) := by
  have := h.pow 2
  simpa using this

end RiemannAnalytic
