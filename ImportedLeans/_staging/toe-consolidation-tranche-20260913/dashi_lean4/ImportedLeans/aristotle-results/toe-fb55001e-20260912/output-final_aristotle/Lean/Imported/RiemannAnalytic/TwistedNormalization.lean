/-
**G11 — relative (twisted) normalization of the compensated anchored
observable.**

`CompensatedObservable` proved the first `α²`-carrying bound for the
compensated observable `𝒟(α) = 𝒜(α) − 𝒜(0)`, but with a constant degrading
like `e^{2AΛ}`: the comparison there is against the **untwisted** baseline
`𝒜(0)`.  This file settles the two questions that degradation raises.

* **The exponential loss is not an artefact of the estimate.**  Against the
  untwisted baseline no constant works: `no_uniform_untwisted_alpha_constant`
  refutes, for a two-frequency configuration, the existence of any `C` with
  `𝒟(α) ≤ C α² s² Var_w(λ)` uniformly over positive weights and frequencies,
  for `|α| < 1/2`.  So the target `compensatedMinor_source_uniformAlpha` is
  **false at that generality**; a proof must use arithmetic structure of the
  log-prime frequencies (or bound the frequency range).

* **Against the twisted mass the exponential loss disappears.**  Using the
  exact identity `cosh(2αλ)−1 = 2 sinh²(αλ)` and the *normalized* distortion
  `1 − sech`, we prove with no restriction whatsoever on `α`

      `𝒟(α) ≤ 8Λ²α² · 𝒜(α)`        (`compensatedMinor_le_twisted_uniform`)
      `𝒟(α) ≤ 8Λ²α² · s²·Var_{w(α)}(λ)`  (`compensatedMinor_le_twisted_varForm`)

  where `𝒜(α)` is the **twisted** anchored mass.  The constant `8Λ²` is
  polynomial in the log-frequency range: the `e^{cΛ}` catastrophe was indeed an
  artefact of normalizing against the wrong baseline, exactly as the relative
  normalization heuristic predicted.

* **But the residual threshold `|α|Λ ≲ 1` is intrinsic, not an artefact.**
  `compensatedMinor_le_twisted_mass` gives the trivial relative bound with
  factor `1`, and `no_uniform_twisted_contraction` shows the factor `1` is
  sharp: the ratio `𝒟(α)/𝒜(α) = 1 − sech(2αΛ)` tends to `1`.  So no *universal*
  relative contraction exists on arbitrary finite frequency sets; the missing
  gain must come either from `|α|Λ = O(1)` or from the distribution of the
  frequencies.

Finally `offLineTarget_excluded_of_twisted_contraction` wires the twisted
relative bound into the `RelativeContraction` endgame: `8Λ²α² < 1` together
with the geometric floor forces `α = 0` exactly.

Nothing here refers to `ζ`, nothing is assumed, and no statement elsewhere is
weakened.
-/
import RiemannAnalytic.CompensatedObservable
import RiemannAnalytic.RelativeContraction

namespace RiemannAnalytic

open Finset

variable {d : ℕ}

/-! ### The exact `sinh²` form of the transverse twist

No Taylor expansion is involved: the compensated weight is *identically*
quadratic in `sinh(αλ)`. -/

/-- `cosh x − 1 = 2 sinh²(x/2)`. -/
theorem cosh_sub_one_eq_two_sinh_sq (x : ℝ) :
    Real.cosh x - 1 = 2 * Real.sinh (x / 2) ^ 2 := by
  have h := Real.cosh_two_mul (x / 2)
  have hc := Real.cosh_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  nlinarith [h, hc]

/-- **The exact compensated weight.**  `w_n(α) − w_n = 2 w_n sinh²(αλ_n)`. -/
theorem coshWeight_sub_eq_sinh_sq (w lam : Fin d → ℝ) (alpha : ℝ) (n : Fin d) :
    coshWeight w lam alpha n - w n = 2 * w n * Real.sinh (alpha * lam n) ^ 2 := by
  have h := cosh_sub_one_eq_two_sinh_sq (2 * alpha * lam n)
  have hhalf : 2 * alpha * lam n / 2 = alpha * lam n := by ring
  rw [hhalf] at h
  unfold coshWeight
  linear_combination w n * h

/-- The exact pair distortion, with no Taylor remainder:
`cosh(2x)cosh(2y) − 1 = 2sinh²x + 2sinh²y + 4 sinh²x sinh²y`. -/
theorem coshProd_sub_one_eq_sinh_sq (x y : ℝ) :
    Real.cosh (2 * x) * Real.cosh (2 * y) - 1
      = 2 * Real.sinh x ^ 2 + 2 * Real.sinh y ^ 2
        + 4 * (Real.sinh x ^ 2 * Real.sinh y ^ 2) := by
  have hx := cosh_sub_one_eq_two_sinh_sq (2 * x)
  have hy := cosh_sub_one_eq_two_sinh_sq (2 * y)
  rw [show 2 * x / 2 = x by ring] at hx
  rw [show 2 * y / 2 = y by ring] at hy
  nlinarith [hx, hy]

/-- **The compensated observable in exact `sinh²` form.**  Every term carries
the transverse twist quadratically, with no expansion and no error term. -/
theorem compensatedMinor_sinh_identity (w lam : Fin d → ℝ) (s alpha : ℝ) :
    compensatedMinor (coshWeight w lam) lam s alpha
      = ∑ n, ∑ m, w n * w m *
          (2 * Real.sinh (alpha * lam n) ^ 2 + 2 * Real.sinh (alpha * lam m) ^ 2
            + 4 * (Real.sinh (alpha * lam n) ^ 2 * Real.sinh (alpha * lam m) ^ 2))
          * (1 - Real.cos (s * (lam n - lam m))) := by
  unfold compensatedMinor minorForm
  rw [coshWeight_zero, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have h := coshProd_sub_one_eq_sinh_sq (alpha * lam n) (alpha * lam m)
  have hn : 2 * (alpha * lam n) = 2 * alpha * lam n := by ring
  have hm : 2 * (alpha * lam m) = 2 * alpha * lam m := by ring
  rw [hn, hm] at h
  unfold coshWeight
  linear_combination (w n * w m * (1 - Real.cos (s * (lam n - lam m)))) * h

/-- **The compensated observable is the twisted mass weighted by `1 − sech·sech`.**
This is the exact relative normalization: instead of comparing `w_n(α) − w_n` to
the untwisted weight, compare it to the twisted one, giving the normalized
distortion `1 − sech(2αλ_n)sech(2αλ_m)`, which is bounded by `1` uniformly in
`αλ` instead of growing exponentially. -/
theorem compensatedMinor_sech_identity (w lam : Fin d → ℝ) (s alpha : ℝ) :
    compensatedMinor (coshWeight w lam) lam s alpha
      = ∑ n, ∑ m, (1 - (1 / Real.cosh (2 * alpha * lam n)) *
            (1 / Real.cosh (2 * alpha * lam m))) *
          (coshWeight w lam alpha n * coshWeight w lam alpha m *
            (1 - Real.cos (s * (lam n - lam m)))) := by
  unfold compensatedMinor minorForm
  rw [coshWeight_zero, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hn : Real.cosh (2 * alpha * lam n) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have hm : Real.cosh (2 * alpha * lam m) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  unfold coshWeight
  field_simp

/-! ### The normalized distortion `1 − sech`, bounded uniformly -/

/-- `cosh x − 1 ≤ x²·cosh x` for every real `x`; equivalently the *normalized*
distortion satisfies `1 − sech x ≤ x²`.  Unlike `cosh x − 1 ≤ (x²/2)e^{|x|}`,
the right-hand side is measured against the **twisted** mass `cosh x`, and the
constant is absolute. -/
theorem cosh_sub_one_le_sq_mul_cosh (x : ℝ) :
    Real.cosh x - 1 ≤ x ^ 2 * Real.cosh x := by
  have h := cosh_sub_one_le (A := |x|) (x := x) le_rfl
  have hexp : Real.exp |x| ≤ 2 * Real.cosh x := by
    rw [Real.cosh_eq]
    rcases abs_cases x with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]
      have := (Real.exp_pos (-x)).le
      linarith
    · rw [he]
      have := (Real.exp_pos x).le
      linarith
  have hx2 : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  nlinarith [h, hexp, hx2]

/-- The pair version: `cosh x cosh y − 1 ≤ (x² + y²)·cosh x cosh y`.  The
distortion of a *pair* of twisted weights, relative to the twisted mass itself,
is bounded by the sum of the squared twists — with no exponential factor and no
restriction on the size of the twist. -/
theorem coshProd_sub_one_le_twisted (x y : ℝ) :
    Real.cosh x * Real.cosh y - 1
      ≤ (x ^ 2 + y ^ 2) * (Real.cosh x * Real.cosh y) := by
  have hA := Real.one_le_cosh x
  have hB := Real.one_le_cosh y
  have hx := cosh_sub_one_le_sq_mul_cosh x
  have hy := cosh_sub_one_le_sq_mul_cosh y
  nlinarith [hx, hy, hA, hB, sq_nonneg x, sq_nonneg y]

/-! ### The twisted relative bounds -/

/-- The twisted second-moment form: the anchored mass of the twisted weights,
weighted by `λ_n² + λ_m²`.  This is the object the relative estimate produces
*before* any supremum in `λ` is taken. -/
noncomputable def twistedMomentForm (w lam : Fin d → ℝ) (s alpha : ℝ) : ℝ :=
  ∑ n, ∑ m, (lam n ^ 2 + lam m ^ 2) *
    (coshWeight w lam alpha n * coshWeight w lam alpha m *
      (1 - Real.cos (s * (lam n - lam m))))

/-- **The relative estimate, kept inside the sum.**  `𝒟(α) ≤ 4α²·M(α)`, where
`M(α)` is the twisted second-moment form.  No supremum over `λ` has been taken,
so no exponential appears; `α` is completely unrestricted. -/
theorem compensatedMinor_le_twisted_moment {w lam : Fin d → ℝ} (s alpha : ℝ)
    (hw : ∀ n, 0 ≤ w n) :
    compensatedMinor (coshWeight w lam) lam s alpha
      ≤ 4 * alpha ^ 2 * twistedMomentForm w lam s alpha := by
  unfold compensatedMinor minorForm twistedMomentForm
  rw [coshWeight_zero, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  have hcos : 0 ≤ 1 - Real.cos (s * (lam n - lam m)) := by
    have := Real.cos_le_one (s * (lam n - lam m)); linarith
  have hww : 0 ≤ w n * w m := mul_nonneg (hw n) (hw m)
  have hkey := coshProd_sub_one_le_twisted (2 * alpha * lam n) (2 * alpha * lam m)
  have hsq : (2 * alpha * lam n) ^ 2 + (2 * alpha * lam m) ^ 2
      = 4 * alpha ^ 2 * (lam n ^ 2 + lam m ^ 2) := by ring
  rw [hsq] at hkey
  have hC : 0 ≤ Real.cosh (2 * alpha * lam n) * Real.cosh (2 * alpha * lam m) :=
    mul_nonneg (Real.cosh_pos _).le (Real.cosh_pos _).le
  have hmain : coshWeight w lam alpha n * coshWeight w lam alpha m - w n * w m
      ≤ 4 * alpha ^ 2 * (lam n ^ 2 + lam m ^ 2) *
        (coshWeight w lam alpha n * coshWeight w lam alpha m) := by
    unfold coshWeight
    nlinarith [mul_le_mul_of_nonneg_left hkey hww]
  nlinarith [mul_le_mul_of_nonneg_right hmain hcos]

/-- **The uniform-in-`α` twisted relative bound.**  With log-frequencies bounded
by `Λ`,

    `𝒟(α) ≤ 8Λ²α²·𝒜(α)`,

where `𝒜(α)` is the anchored mass of the twisted weights.  The constant is
polynomial in `Λ` and **independent of `α`** — in particular it is uniform on
the whole strip `0 < |α| < 1/2`, which the untwisted comparison provably cannot
be (`no_uniform_untwisted_alpha_constant`). -/
theorem compensatedMinor_le_twisted_uniform {w lam : Fin d → ℝ} {s alpha Lam : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hLam : ∀ n, |lam n| ≤ Lam) :
    compensatedMinor (coshWeight w lam) lam s alpha
      ≤ 8 * Lam ^ 2 * alpha ^ 2 * minorForm (coshWeight w lam alpha) lam s := by
  have hsq : ∀ n : Fin d, lam n ^ 2 ≤ Lam ^ 2 := by
    intro n
    have h := hLam n
    nlinarith [abs_nonneg (lam n), sq_abs (lam n), le_trans (abs_nonneg (lam n)) h]
  have hstep := compensatedMinor_le_twisted_moment (w := w) (lam := lam) s alpha hw
  have hmoment : twistedMomentForm w lam s alpha
      ≤ 2 * Lam ^ 2 * minorForm (coshWeight w lam alpha) lam s := by
    unfold twistedMomentForm minorForm
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m _ => ?_
    have hcos : 0 ≤ 1 - Real.cos (s * (lam n - lam m)) := by
      have := Real.cos_le_one (s * (lam n - lam m)); linarith
    have hWn : 0 ≤ coshWeight w lam alpha n :=
      mul_nonneg (hw n) (Real.cosh_pos _).le
    have hWm : 0 ≤ coshWeight w lam alpha m :=
      mul_nonneg (hw m) (Real.cosh_pos _).le
    have hbase : 0 ≤ coshWeight w lam alpha n * coshWeight w lam alpha m *
        (1 - Real.cos (s * (lam n - lam m))) :=
      mul_nonneg (mul_nonneg hWn hWm) hcos
    have hfac : lam n ^ 2 + lam m ^ 2 ≤ 2 * Lam ^ 2 := by
      have := hsq n; have := hsq m; linarith
    exact mul_le_mul_of_nonneg_right hfac hbase
  have halpha : 0 ≤ 4 * alpha ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hmoment halpha
  calc compensatedMinor (coshWeight w lam) lam s alpha
      ≤ 4 * alpha ^ 2 * twistedMomentForm w lam s alpha := hstep
    _ ≤ 4 * alpha ^ 2 * (2 * Lam ^ 2 * minorForm (coshWeight w lam alpha) lam s) := this
    _ = 8 * Lam ^ 2 * alpha ^ 2 * minorForm (coshWeight w lam alpha) lam s := by ring

/-- **The relative variance inequality.**  Composing the twisted relative bound
with the log-variance ledger gives

    `𝒟(α) ≤ 8Λ²α²·s²·Var_{w(α)}(λ)`,

i.e. the compensated observable is controlled by the **twisted** variance
`𝒱_α`, with a constant free of any exponential in `α`. -/
theorem compensatedMinor_le_twisted_varForm {w lam : Fin d → ℝ} {s alpha Lam : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hLam : ∀ n, |lam n| ≤ Lam) :
    compensatedMinor (coshWeight w lam) lam s alpha
      ≤ 8 * Lam ^ 2 * alpha ^ 2 * (s ^ 2 * varForm (coshWeight w lam alpha) lam) := by
  have hWnonneg : ∀ n, 0 ≤ coshWeight w lam alpha n := fun n =>
    mul_nonneg (hw n) (Real.cosh_pos _).le
  have hled := minorForm_le_varForm (w := coshWeight w lam alpha) (lam := lam) hWnonneg s
  have hbase := compensatedMinor_le_twisted_uniform (s := s) (alpha := alpha) (Lam := Lam) hw hLam
  have hfac : 0 ≤ 8 * Lam ^ 2 * alpha ^ 2 := by positivity
  exact hbase.trans (mul_le_mul_of_nonneg_left hled hfac)

/-- **The exact arithmetic condition, with the sup replaced by an average.**
The supremum `Λ²` is not what the estimate really needs: only the
*kernel-weighted mean square* of the log-frequencies enters.  If the twisted
second-moment form is at most `Q` times the twisted mass — i.e. the anchored
kernel sees mean square log-frequency at most `Q` — then
`𝒟(α) ≤ 4Qα²·𝒜(α)`. -/
theorem compensatedMinor_le_of_meanSquare {w lam : Fin d → ℝ} {s alpha Q : ℝ}
    (hw : ∀ n, 0 ≤ w n)
    (hQ : twistedMomentForm w lam s alpha
      ≤ Q * minorForm (coshWeight w lam alpha) lam s) :
    compensatedMinor (coshWeight w lam) lam s alpha
      ≤ 4 * Q * alpha ^ 2 * minorForm (coshWeight w lam alpha) lam s := by
  have hstep := compensatedMinor_le_twisted_moment (w := w) (lam := lam) s alpha hw
  have hfac : (0 : ℝ) ≤ 4 * alpha ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hQ hfac
  calc compensatedMinor (coshWeight w lam) lam s alpha
      ≤ 4 * alpha ^ 2 * twistedMomentForm w lam s alpha := hstep
    _ ≤ 4 * alpha ^ 2 * (Q * minorForm (coshWeight w lam alpha) lam s) := this
    _ = 4 * Q * alpha ^ 2 * minorForm (coshWeight w lam alpha) lam s := by ring

/-- **The sharp pointwise criterion.**  If the normalized distortion
`1 − sech(2αλ_n)sech(2αλ_m)` is at most `η` for every pair of frequencies, then
`𝒟(α) ≤ η·𝒜(α)`.  By `compensatedMinor_sech_identity` this criterion is exactly
what the relative bound needs — nothing is thrown away. -/
theorem compensatedMinor_le_of_pointwise_distortion {w lam : Fin d → ℝ} {s alpha eta : ℝ}
    (hw : ∀ n, 0 ≤ w n)
    (heta : ∀ n m : Fin d,
      1 - (1 / Real.cosh (2 * alpha * lam n)) * (1 / Real.cosh (2 * alpha * lam m)) ≤ eta) :
    compensatedMinor (coshWeight w lam) lam s alpha
      ≤ eta * minorForm (coshWeight w lam alpha) lam s := by
  rw [compensatedMinor_sech_identity]
  unfold minorForm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  have hcos : 0 ≤ 1 - Real.cos (s * (lam n - lam m)) := by
    have := Real.cos_le_one (s * (lam n - lam m)); linarith
  have hWn : 0 ≤ coshWeight w lam alpha n := mul_nonneg (hw n) (Real.cosh_pos _).le
  have hWm : 0 ≤ coshWeight w lam alpha m := mul_nonneg (hw m) (Real.cosh_pos _).le
  exact mul_le_mul_of_nonneg_right (heta n m) (mul_nonneg (mul_nonneg hWn hWm) hcos)

/-- The normalized distortion under a bounded twist: `|x|,|y| ≤ B` gives
`1 − sech x sech y ≤ 1 − sech²B`. -/
theorem one_sub_sech_prod_le_of_bounded_twist {x y B : ℝ} (hx : |x| ≤ B) (hy : |y| ≤ B) :
    1 - (1 / Real.cosh x) * (1 / Real.cosh y) ≤ 1 - 1 / Real.cosh B ^ 2 := by
  have hB : 0 ≤ B := le_trans (abs_nonneg x) hx
  have habsB : |B| = B := abs_of_nonneg hB
  have hcx : Real.cosh x ≤ Real.cosh B := Real.cosh_le_cosh.mpr (by rw [habsB]; exact hx)
  have hcy : Real.cosh y ≤ Real.cosh B := Real.cosh_le_cosh.mpr (by rw [habsB]; exact hy)
  have hpx : 0 < Real.cosh x := Real.cosh_pos x
  have hpy : 0 < Real.cosh y := Real.cosh_pos y
  have hpB : 0 < Real.cosh B := Real.cosh_pos B
  have hx' : 1 / Real.cosh B ≤ 1 / Real.cosh x := one_div_le_one_div_of_le hpx hcx
  have hy' : 1 / Real.cosh B ≤ 1 / Real.cosh y := one_div_le_one_div_of_le hpy hcy
  have hBpos : 0 < 1 / Real.cosh B := by positivity
  have hsq : 1 / Real.cosh B ^ 2 = (1 / Real.cosh B) * (1 / Real.cosh B) := by
    rw [pow_two]; field_simp
  have hprod : (1 / Real.cosh B) * (1 / Real.cosh B)
      ≤ (1 / Real.cosh x) * (1 / Real.cosh y) :=
    mul_le_mul hx' hy' hBpos.le (by positivity)
  rw [hsq]; linarith [hprod]

/-- **Strict contraction under a bounded twist.**  With log-frequencies bounded
by `Λ`,

    `𝒟(α) ≤ (1 − sech²(2|α|Λ))·𝒜(α)`,

and the factor is `< 1` for every finite twist.  (It degrades to `1`
exponentially as `|α|Λ → ∞`, which is precisely what
`no_uniform_twisted_contraction` shows is unavoidable; the quantitatively useful
regime is `|α|Λ = O(1)`, where `compensatedMinor_le_twisted_uniform` gives the
polynomial factor `8Λ²α²`.) -/
theorem compensatedMinor_le_bounded_twist {w lam : Fin d → ℝ} {s alpha Lam : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hLam : ∀ n, |lam n| ≤ Lam) :
    compensatedMinor (coshWeight w lam) lam s alpha
      ≤ (1 - 1 / Real.cosh (2 * |alpha| * Lam) ^ 2)
        * minorForm (coshWeight w lam alpha) lam s := by
  refine compensatedMinor_le_of_pointwise_distortion hw fun n m => ?_
  have hbound : ∀ k : Fin d, |2 * alpha * lam k| ≤ 2 * |alpha| * Lam := by
    intro k
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    have hk : |alpha| * |lam k| ≤ |alpha| * Lam :=
      mul_le_mul_of_nonneg_left (hLam k) (abs_nonneg alpha)
    linarith
  exact one_sub_sech_prod_le_of_bounded_twist (hbound n) (hbound m)

/-- The bounded-twist contraction factor is strictly below `1`. -/
theorem bounded_twist_factor_lt_one (B : ℝ) : 1 - 1 / Real.cosh B ^ 2 < 1 := by
  have hB : 0 < Real.cosh B := Real.cosh_pos B
  have : 0 < 1 / Real.cosh B ^ 2 := by positivity
  linarith

/-- **The reciprocal regime, cleanly.**  If `|α|Λ ≤ 1/4` then the twisted
relative factor is at most `1/2`: a strict contraction, with no exponential and
no hypothesis beyond the twist being bounded. -/
theorem twisted_relative_factor_le_half {alpha Lam : ℝ} (hLam0 : 0 ≤ Lam)
    (h : |alpha| * Lam ≤ 1 / 4) :
    8 * Lam ^ 2 * alpha ^ 2 ≤ 1 / 2 := by
  have habs : 0 ≤ |alpha| := abs_nonneg alpha
  have hsq : alpha ^ 2 = |alpha| ^ 2 := (sq_abs alpha).symm
  have hprod : (|alpha| * Lam) ^ 2 ≤ (1 / 4) ^ 2 := by
    have hp : 0 ≤ |alpha| * Lam := mul_nonneg habs hLam0
    nlinarith [h, hp]
  nlinarith [hprod, hsq]

/-- The trivial relative bound with factor `1`: the compensated observable never
exceeds the twisted mass.  (`no_uniform_twisted_contraction` shows the factor
`1` cannot be improved uniformly.) -/
theorem compensatedMinor_le_twisted_mass {w lam : Fin d → ℝ} (s alpha : ℝ)
    (hw : ∀ n, 0 ≤ w n) :
    compensatedMinor (coshWeight w lam) lam s alpha
      ≤ minorForm (coshWeight w lam alpha) lam s := by
  unfold compensatedMinor minorForm
  rw [coshWeight_zero, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun m _ => ?_
  have hcos : 0 ≤ 1 - Real.cos (s * (lam n - lam m)) := by
    have := Real.cos_le_one (s * (lam n - lam m)); linarith
  have hww : 0 ≤ w n * w m := mul_nonneg (hw n) (hw m)
  nlinarith [mul_nonneg hww hcos]

/-! ### A block-localized, `α²`-carrying twisted budget -/

/-- The weight-level block bound for the log-variance: if all log-frequencies
lie in an interval of length `ℓ` then `Var_w(λ) ≤ (∑w)²ℓ²`. -/
theorem varForm_le_block {w lam : Fin d → ℝ} {c l : ℝ} (hw : ∀ n, 0 ≤ w n) (hl : 0 ≤ l)
    (hblock : ∀ n, lam n ∈ Set.Icc c (c + l)) :
    varForm w lam ≤ (∑ n, w n) ^ 2 * l ^ 2 := by
  have h := logVariance_le_block (fun n => ((Real.sqrt (w n) : ℝ) : ℂ)) lam hl hblock
  rw [logVariance, ampWeight_sqrt hw] at h
  exact h

/-- **The assembled twisted budget.**  With log-frequencies bounded by `Λ` and
confined to a log-block of length `ℓ`, the compensated observable obeys

    `𝒟(α) ≤ 8Λ²α²·s²·(∑ w(α))²ℓ²`,

an `α²`-carrying bound whose localization gain is carried by `ℓ` and whose
constant contains no exponential in `α`. -/
theorem compensatedMinor_le_twisted_block {w lam : Fin d → ℝ} {s alpha Lam c l : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hLam : ∀ n, |lam n| ≤ Lam) (hl : 0 ≤ l)
    (hblock : ∀ n, lam n ∈ Set.Icc c (c + l)) :
    compensatedMinor (coshWeight w lam) lam s alpha
      ≤ 8 * Lam ^ 2 * alpha ^ 2 *
        (s ^ 2 * ((∑ n, coshWeight w lam alpha n) ^ 2 * l ^ 2)) := by
  have hWnonneg : ∀ n, 0 ≤ coshWeight w lam alpha n := fun n =>
    mul_nonneg (hw n) (Real.cosh_pos _).le
  have hblk := varForm_le_block (w := coshWeight w lam alpha) (lam := lam) hWnonneg hl hblock
  have hbase := compensatedMinor_le_twisted_varForm (s := s) (alpha := alpha) (Lam := Lam) hw hLam
  have hfac : (0 : ℝ) ≤ 8 * Lam ^ 2 * alpha ^ 2 * s ^ 2 := by positivity
  have hstep : 8 * Lam ^ 2 * alpha ^ 2 * (s ^ 2 * varForm (coshWeight w lam alpha) lam)
      ≤ 8 * Lam ^ 2 * alpha ^ 2 *
        (s ^ 2 * ((∑ n, coshWeight w lam alpha n) ^ 2 * l ^ 2)) := by
    have := mul_le_mul_of_nonneg_left hblk hfac
    calc 8 * Lam ^ 2 * alpha ^ 2 * (s ^ 2 * varForm (coshWeight w lam alpha) lam)
        = 8 * Lam ^ 2 * alpha ^ 2 * s ^ 2 * varForm (coshWeight w lam alpha) lam := by ring
      _ ≤ 8 * Lam ^ 2 * alpha ^ 2 * s ^ 2 * ((∑ n, coshWeight w lam alpha n) ^ 2 * l ^ 2) :=
          this
      _ = 8 * Lam ^ 2 * alpha ^ 2 *
            (s ^ 2 * ((∑ n, coshWeight w lam alpha n) ^ 2 * l ^ 2)) := by ring
  exact hbase.trans hstep

/-! ### Wiring the twisted bound into the contraction endgame -/

/-- **The endgame consumes the twisted bound directly.**  If the anchored defect
`D` is at least the geometric floor `cL⁶α²`, is dominated by the compensated
observable, dominates the twisted mass, and the reciprocal condition
`8Λ²α² < 1` holds, then the displacement is exactly `0` — no shrinking tube. -/
theorem offLineTarget_excluded_of_twisted_contraction
    {w lam : Fin d → ℝ} {s alpha Lam c L D : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hLam : ∀ n, |lam n| ≤ Lam)
    (hc : 0 < c) (hL : 0 < L) (hD0 : 0 ≤ D)
    (hsmall : 8 * Lam ^ 2 * alpha ^ 2 < 1)
    (hfloor : c * L ^ 6 * alpha ^ 2 ≤ D)
    (hlower : D ≤ compensatedMinor (coshWeight w lam) lam s alpha)
    (hmass : minorForm (coshWeight w lam alpha) lam s ≤ D) :
    alpha = 0 := by
  have hbase := compensatedMinor_le_twisted_uniform (s := s) (alpha := alpha) (Lam := Lam) hw hLam
  have hfac : 0 ≤ 8 * Lam ^ 2 * alpha ^ 2 := by positivity
  have hcontract : D ≤ (8 * Lam ^ 2 * alpha ^ 2) * D :=
    hlower.trans (hbase.trans (mul_le_mul_of_nonneg_left hmass hfac))
  exact offLineTarget_excluded_of_relative_budget hc hL hD0 hsmall hfloor hcontract

/-! ### The two obstruction theorems

Both are proved on an explicit two-frequency configuration:
`d = 2`, `w = (1,1)`, `λ = (0,Λ)`, `s = π/Λ`, `α = 1/4`.  Then

* `𝒜(0) = 4`,  `𝒜(α) = 4cosh(Λ/2)`,  `𝒟(α) = 4(cosh(Λ/2) − 1)`,
* `Var_w(λ) = Λ²`, `s²Var_w(λ) = π²`.
-/

/-- `cosh x ≥ 1 + x²/2`. -/
theorem one_add_half_sq_le_cosh (x : ℝ) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have h := cosh_sub_one_eq_two_sinh_sq x
  have hsq : (x / 2) ^ 2 ≤ Real.sinh (x / 2) ^ 2 := by
    rcases le_total 0 (x / 2) with hx | hx
    · rcases eq_or_lt_of_le hx with hx0 | hx0
      · rw [← hx0]; simp
      · have hs : x / 2 < Real.sinh (x / 2) := Real.self_lt_sinh_iff.mpr hx0
        nlinarith [hs, hx0]
    · rcases eq_or_lt_of_le hx with hx0 | hx0
      · rw [hx0]; simp
      · have hs : Real.sinh (x / 2) < x / 2 := Real.sinh_lt_self_iff.mpr hx0
        nlinarith [hs, hx0]
  nlinarith [h, hsq]

/-- The two-frequency configuration: weights. -/
private noncomputable def ceW : Fin 2 → ℝ := fun _ => 1

/-- The two-frequency configuration: log-frequencies `(0, Λ)`. -/
private noncomputable def ceLam (Lam : ℝ) : Fin 2 → ℝ := ![0, Lam]

private theorem ceW_nonneg : ∀ n, 0 ≤ ceW n := by intro n; simp [ceW]

private theorem ce_minorForm (Lam : ℝ) (hL : 0 < Lam) (W : Fin 2 → ℝ) :
    minorForm W (ceLam Lam) (Real.pi / Lam) = 4 * (W 0 * W 1) := by
  have hne : Lam ≠ 0 := ne_of_gt hL
  have h1 : Real.pi / Lam * (ceLam Lam 0 - ceLam Lam 1) = -Real.pi := by
    simp only [ceLam, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  have h2 : Real.pi / Lam * (ceLam Lam 1 - ceLam Lam 0) = Real.pi := by
    simp only [ceLam, Matrix.cons_val_zero, Matrix.cons_val_one]
    field_simp
    ring
  have h0 : Real.pi / Lam * (ceLam Lam 0 - ceLam Lam 0) = 0 := by ring
  have h3 : Real.pi / Lam * (ceLam Lam 1 - ceLam Lam 1) = 0 := by ring
  simp only [minorForm, Fin.sum_univ_two, h0, h1, h2, h3, Real.cos_neg, Real.cos_pi,
    Real.cos_zero]
  ring

private theorem ce_varForm (Lam : ℝ) :
    varForm ceW (ceLam Lam) = Lam ^ 2 := by
  simp only [varForm, ceW, ceLam, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

private theorem ce_minor_zero (Lam : ℝ) (hL : 0 < Lam) :
    minorForm (coshWeight ceW (ceLam Lam) 0) (ceLam Lam) (Real.pi / Lam) = 4 := by
  rw [coshWeight_zero, ce_minorForm Lam hL]
  norm_num [ceW]

private theorem ce_minor_quarter (Lam : ℝ) (hL : 0 < Lam) :
    minorForm (coshWeight ceW (ceLam Lam) (1 / 4)) (ceLam Lam) (Real.pi / Lam)
      = 4 * Real.cosh (Lam / 2) := by
  rw [ce_minorForm Lam hL]
  have h0 : coshWeight ceW (ceLam Lam) (1 / 4) 0 = 1 := by
    show ceW 0 * Real.cosh (2 * (1 / 4) * ceLam Lam 0) = 1
    have e0 : ceLam Lam 0 = 0 := rfl
    rw [e0]
    norm_num [ceW]
  have h1 : coshWeight ceW (ceLam Lam) (1 / 4) 1 = Real.cosh (Lam / 2) := by
    show ceW 1 * Real.cosh (2 * (1 / 4) * ceLam Lam 1) = Real.cosh (Lam / 2)
    have e1 : ceLam Lam 1 = Lam := rfl
    have e2 : 2 * (1 / 4 : ℝ) * Lam = Lam / 2 := by ring
    rw [e1, e2]
    norm_num [ceW]
  rw [h0, h1]; ring

/-- **No uniform untwisted constant exists.**  There is no `C` for which the
compensated observable obeys `𝒟(α) ≤ C α² s² Var_w(λ)` uniformly over
nonnegative weights, log-frequencies and `|α| < 1/2`.  Hence the proposed
`compensatedMinor_source_uniformAlpha` is **false** at that generality: with the
untwisted baseline the exponential degradation of
`CompensatedObservable.compensatedMinor_cosh_le` is genuine, not an artefact of
the proof, and any full-strip statement must use structure of the log-prime
frequencies (or restrict their range). -/
theorem no_uniform_untwisted_alpha_constant :
    ¬ ∃ C : ℝ, ∀ (w lam : Fin 2 → ℝ) (s alpha : ℝ),
        (∀ n, 0 ≤ w n) → |alpha| < 1 / 2 →
        compensatedMinor (coshWeight w lam) lam s alpha
          ≤ C * alpha ^ 2 * (s ^ 2 * varForm w lam) := by
  rintro ⟨C, hC⟩
  set Lam : ℝ := |C| + 4 with hLamdef
  have hL : 0 < Lam := by rw [hLamdef]; linarith [abs_nonneg C]
  have hkey := hC ceW (ceLam Lam) (Real.pi / Lam) (1 / 4) ceW_nonneg (by
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 4)]; norm_num)
  -- evaluate both sides
  have hvar : varForm ceW (ceLam Lam) = Lam ^ 2 := ce_varForm Lam
  simp only [compensatedMinor] at hkey
  rw [ce_minor_zero Lam hL, ce_minor_quarter Lam hL, hvar] at hkey
  -- the right-hand side is `Cπ²/16`, the left-hand side is at least `Λ²/2`
  have hpi : (Real.pi / Lam) ^ 2 * Lam ^ 2 = Real.pi ^ 2 := by
    field_simp
  have hcosh : 1 + (Lam / 2) ^ 2 / 2 ≤ Real.cosh (Lam / 2) := one_add_half_sq_le_cosh _
  have hpi2 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_le_four, Real.pi_pos]
  have habs : 0 ≤ |C| := abs_nonneg C
  have hrhs : C * (1 / 4 : ℝ) ^ 2 * ((Real.pi / Lam) ^ 2 * Lam ^ 2)
      = C * Real.pi ^ 2 / 16 := by rw [hpi]; ring
  have hrhsle : C * Real.pi ^ 2 / 16 ≤ |C| := by
    rcases le_total 0 C with h | h
    · rw [abs_of_nonneg h]; nlinarith [hpi2, h]
    · rw [abs_of_nonpos h]; nlinarith [hpi2, h, sq_nonneg Real.pi]
  have hLamsq : Lam ^ 2 = (|C| + 4) ^ 2 := by rw [hLamdef]
  nlinarith [hkey, hcosh, habs, hrhs, hrhsle, hLamsq, sq_nonneg |C|]

/-- **No universal relative contraction exists either.**  There is no `η < 1`
with `𝒟(α) ≤ η·𝒜(α)` uniformly over nonnegative weights, log-frequencies and
`|α| < 1/2`: on the two-frequency configuration the ratio is exactly
`1 − sech(2αΛ) → 1`.  So the factor `1` of `compensatedMinor_le_twisted_mass` is
sharp, and the gain `η(T) < 1` demanded by the endgame cannot come from the
hyperbolic weights alone — it must come from `|α|Λ = O(1)` (which
`compensatedMinor_le_twisted_uniform` supplies, with a polynomial constant) or
from the distribution of the frequencies. -/
theorem no_uniform_twisted_contraction :
    ¬ ∃ eta : ℝ, eta < 1 ∧ ∀ (w lam : Fin 2 → ℝ) (s alpha : ℝ),
        (∀ n, 0 ≤ w n) → |alpha| < 1 / 2 →
        compensatedMinor (coshWeight w lam) lam s alpha
          ≤ eta * minorForm (coshWeight w lam alpha) lam s := by
  rintro ⟨eta, heta, hbound⟩
  set eps : ℝ := 1 - eta with hepsdef
  have heps : 0 < eps := by rw [hepsdef]; linarith
  set Lam : ℝ := 4 + 8 / eps with hLamdef
  have hdiv : 0 < 8 / eps := by positivity
  have hL : 0 < Lam := by rw [hLamdef]; linarith
  have hLam4 : (4 : ℝ) ≤ Lam := by rw [hLamdef]; linarith
  have hepsLam : (8 : ℝ) ≤ eps * Lam := by
    have hid : eps * Lam = 4 * eps + 8 := by
      rw [hLamdef]; field_simp
    rw [hid]; linarith
  have hkey := hbound ceW (ceLam Lam) (Real.pi / Lam) (1 / 4) ceW_nonneg (by
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 4)]; norm_num)
  simp only [compensatedMinor] at hkey
  rw [ce_minor_zero Lam hL, ce_minor_quarter Lam hL] at hkey
  -- `4cosh − 4 ≤ η·4cosh` means `ε·cosh(Λ/2) ≤ 1`, but `ε·cosh(Λ/2) ≥ 4`
  have hcosh : 1 + (Lam / 2) ^ 2 / 2 ≤ Real.cosh (Lam / 2) := one_add_half_sq_le_cosh _
  have h32 : (32 : ℝ) ≤ eps * Lam ^ 2 := by nlinarith [hepsLam, hLam4]
  have hbig : (4 : ℝ) ≤ eps * (1 + (Lam / 2) ^ 2 / 2) := by nlinarith [h32, heps]
  have hmul : eps * (1 + (Lam / 2) ^ 2 / 2) ≤ eps * Real.cosh (Lam / 2) :=
    mul_le_mul_of_nonneg_left hcosh heps.le
  nlinarith [hkey, hbig, hmul, hepsdef]

end RiemannAnalytic
