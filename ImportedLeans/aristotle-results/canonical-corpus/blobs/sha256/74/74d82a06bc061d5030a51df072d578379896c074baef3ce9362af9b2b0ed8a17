/-
**G12 — the literal log-frequency structure of the compensated prime kernel.**

`CompensatedDiagonal` proved, abstractly, that the compensated anchored
observable vanishes exactly on the diagonal and is controlled by the
second-difference form `∑ₙ∑ₘ wₙwₘ(λₙ−λₘ)²`.  On the prime side the
log-frequencies are literally `λₙ = log n`, so the second difference is

    `λₙ − λₘ = log(n/m)`,

and the near-diagonal model `log(n/m) ≈ (n−m)/m` has to be an inequality, not an
approximation, before it can be used.  This file supplies exactly that, with no
asymptotics and no unproved constants:

* `log_sub_log_le_div`, `abs_log_sub_log_le` — the two-sided literal bound
  `|log a − log b| ≤ |a − b| / M` for `a, b ≥ M > 0`;
* `log_ratio_two_sided` — the sharp form `(n−m)/n ≤ log(n/m) ≤ (n−m)/m`, which
  is the exact meaning of the near-diagonal model `λ ≍ h/m`;
* `log_ratio_sq_le` — its square, the factor the compensated kernel carries;
* `logFreq_eq_iff` — the diagonal is exactly `n = m`: the quadratic zero of the
  compensated kernel sits on the prime diagonal and nowhere else;
* `minorForm_logFreq_le_secondDifference` — the literal statement that on a
  block of integers `≥ M` the anchored observable is bounded by the
  **second-difference-weighted prime correlation sum**

      `(s²/2M²)·∑ₙ∑ₘ wₙwₘ(n−m)²`,

  which is the object `nearDiagonalPrimeVarianceBound` has to estimate.

Nothing here mentions `ζ`; these are the exact literal inequalities that the
prime-side estimate is allowed to use.
-/
import RiemannAnalytic.CompensatedDiagonal

namespace RiemannAnalytic

open Finset

/-! ### Literal bounds for differences of logarithms -/

/-- `log a − log b ≤ (a − b)/M` for `M ≤ b ≤ a`. -/
theorem log_sub_log_le_div {a b M : ℝ} (hM : 0 < M) (hb : M ≤ b) (hab : b ≤ a) :
    Real.log a - Real.log b ≤ (a - b) / M := by
  have hb0 : 0 < b := lt_of_lt_of_le hM hb
  have ha0 : 0 < a := lt_of_lt_of_le hb0 hab
  have h1 : Real.log a - Real.log b = Real.log (a / b) :=
    (Real.log_div (ne_of_gt ha0) (ne_of_gt hb0)).symm
  have h2 : Real.log (a / b) ≤ a / b - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h3 : (a - b) / b = a / b - 1 := by rw [sub_div, div_self (ne_of_gt hb0)]
  have h4 : (a - b) / b ≤ (a - b) / M := by
    gcongr
    linarith
  linarith [h1.le, h1.ge, h2, h3.le, h3.ge, h4]


/-- The literal two-sided bound `|log a − log b| ≤ |a − b|/M` on `[M, ∞)`. -/
theorem abs_log_sub_log_le {a b M : ℝ} (hM : 0 < M) (ha : M ≤ a) (hb : M ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / M := by
  rcases le_total b a with hba | hab
  · have hkey := log_sub_log_le_div hM hb hba
    have hmono : Real.log b ≤ Real.log a := Real.log_le_log (lt_of_lt_of_le hM hb) hba
    have h1 : (0 : ℝ) ≤ Real.log a - Real.log b := by linarith
    have h2 : (0 : ℝ) ≤ a - b := by linarith
    rw [abs_of_nonneg h1, abs_of_nonneg h2]
    exact hkey
  · have hkey := log_sub_log_le_div hM ha hab
    have hmono : Real.log a ≤ Real.log b := Real.log_le_log (lt_of_lt_of_le hM ha) hab
    have h1 : Real.log a - Real.log b ≤ 0 := by linarith
    have h2 : a - b ≤ 0 := by linarith
    rw [abs_of_nonpos h1, abs_of_nonpos h2]
    have hrw : -(a - b) / M = (b - a) / M := by ring
    rw [hrw]
    linarith [hkey]

/-- **The exact near-diagonal model.**  For `0 < m ≤ n`,

    `(n − m)/n ≤ log(n/m) ≤ (n − m)/m`,

so the log-frequency difference really is `≍ (n−m)/m` in the near-diagonal
range — as an inequality, not an approximation. -/
theorem log_ratio_two_sided {m n : ℝ} (hm : 0 < m) (hmn : m ≤ n) :
    (n - m) / n ≤ Real.log n - Real.log m ∧ Real.log n - Real.log m ≤ (n - m) / m := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  constructor
  · have h1 : Real.log m - Real.log n = Real.log (m / n) :=
      (Real.log_div (ne_of_gt hm) (ne_of_gt hn)).symm
    have h2 : Real.log (m / n) ≤ m / n - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h3 : (n - m) / n = 1 - m / n := by rw [sub_div, div_self (ne_of_gt hn)]
    linarith [h1.le, h1.ge, h2, h3.le, h3.ge]
  · exact log_sub_log_le_div hm le_rfl hmn

/-- The squared near-diagonal model: `(log(n/m))² ≤ (n−m)²/M²` on a block of
reals `≥ M`. -/
theorem log_ratio_sq_le {a b M : ℝ} (hM : 0 < M) (ha : M ≤ a) (hb : M ≤ b) :
    (Real.log a - Real.log b) ^ 2 ≤ (a - b) ^ 2 / M ^ 2 := by
  have habs := abs_log_sub_log_le hM ha hb
  have h0 : 0 ≤ |Real.log a - Real.log b| := abs_nonneg _
  have hsq : |Real.log a - Real.log b| ^ 2 ≤ (|a - b| / M) ^ 2 := by
    nlinarith [habs, h0, abs_nonneg (a - b), hM]
  rw [sq_abs] at hsq
  rw [div_pow, sq_abs] at hsq
  exact hsq

/-- **The diagonal is exactly the prime diagonal.**  For positive integers the
log-frequencies coincide precisely when the integers do, so the quadratic zero
of the compensated kernel sits on `n = m` and nowhere else. -/
theorem logFreq_eq_iff {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    Real.log n = Real.log m ↔ n = m := by
  constructor
  · intro h
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have : (n : ℝ) = m := Real.log_injOn_pos (Set.mem_setOf.mpr hn') (Set.mem_setOf.mpr hm') h
    exact_mod_cast this
  · intro h; rw [h]

/-! ### The literal second-difference prime sum -/

variable {d : ℕ}

/-- **The literal near/far input.**  On a block of integers `≥ M`, with
log-frequencies `λₙ = log Nₙ`, the anchored observable is bounded by the
second-difference-weighted correlation sum

    `(s²/2M²)·∑ₙ∑ₘ wₙwₘ(Nₙ − Nₘ)²`.

The diagonal contributes exactly `0`, since `Nₙ − Nₙ = 0`; this is the exact
object the remaining prime-side estimate must bound. -/
theorem minorForm_logFreq_le_secondDifference {w : Fin d → ℝ} {N : Fin d → ℕ}
    {M s : ℝ} (hw : ∀ n, 0 ≤ w n) (hM : 0 < M) (hN : ∀ n, M ≤ (N n : ℝ)) :
    minorForm w (fun n => Real.log (N n)) s
      ≤ s ^ 2 / (2 * M ^ 2) * ∑ n, ∑ m, w n * w m * ((N n : ℝ) - (N m : ℝ)) ^ 2 := by
  unfold minorForm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  have hk : 1 - Real.cos (s * (Real.log (N n) - Real.log (N m)))
      ≤ (s * (Real.log (N n) - Real.log (N m))) ^ 2 / 2 :=
    one_sub_cos_le_half_sq _
  have hlog := log_ratio_sq_le hM (hN n) (hN m)
  have hM2 : 0 < M ^ 2 := by positivity
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have hstep : (s * (Real.log (N n) - Real.log (N m))) ^ 2 / 2
      ≤ s ^ 2 / (2 * M ^ 2) * ((N n : ℝ) - (N m : ℝ)) ^ 2 := by
    have hmul : s ^ 2 * (Real.log (N n) - Real.log (N m)) ^ 2
        ≤ s ^ 2 * (((N n : ℝ) - (N m : ℝ)) ^ 2 / M ^ 2) :=
      mul_le_mul_of_nonneg_left hlog hs2
    have hrw : s ^ 2 / (2 * M ^ 2) * ((N n : ℝ) - (N m : ℝ)) ^ 2
        = s ^ 2 * (((N n : ℝ) - (N m : ℝ)) ^ 2 / M ^ 2) / 2 := by
      field_simp
    rw [hrw, mul_pow]
    linarith [hmul]
  have hww : 0 ≤ w n * w m := mul_nonneg (hw n) (hw m)
  nlinarith [mul_le_mul_of_nonneg_left (hk.trans hstep) hww]

/-- The diagonal terms of the literal second-difference prime sum vanish
exactly. -/
theorem secondDifference_diag_zero (w : Fin d → ℝ) (N : Fin d → ℕ) (n : Fin d) :
    w n * w n * ((N n : ℝ) - (N n : ℝ)) ^ 2 = 0 := by simp

/-! ### What the actual von Mangoldt coefficients give, with trivial input

The question posed for the compensated prime kernel is whether the quadratic
diagonal zero produces a *relative gain* `δ(T) → 0`.  The next theorem records
exactly what the trivial coefficient bound `Λ(n) ≤ log n` gives on a dyadic
block: the second-difference prime sum is at most `(log 2M)²(M+1)²`, i.e. the
full trivial size of the block — the quadratic factor `(log(n/m))² ≤ (log 2)²`
contributes a *constant*, not a vanishing factor.  So the trivial input provably
yields no `δ(T) → 0`, and the missing estimate genuinely has to see cancellation
in the prime correlations. -/
theorem vonMangoldt_block_secondDifference_le (M : ℕ) (hM : 0 < M) :
    ∑ n ∈ Finset.Icc M (2 * M), ∑ m ∈ Finset.Icc M (2 * M),
        ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m
          * (Real.log n - Real.log m) ^ 2
      ≤ Real.log (2 * M) ^ 2 * (M + 1) ^ 2 := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hlogM : 0 ≤ Real.log (2 * M) := by
    apply Real.log_nonneg
    linarith
  have hterm : ∀ n ∈ Finset.Icc M (2 * M), ∀ m ∈ Finset.Icc M (2 * M),
      ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m
          * (Real.log n - Real.log m) ^ 2 ≤ Real.log (2 * M) ^ 2 := by
    intro n hn m hm
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    obtain ⟨hm1, hm2⟩ := Finset.mem_Icc.mp hm
    have hnr : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hnr2 : (n : ℝ) ≤ 2 * M := by exact_mod_cast hn2
    have hmr : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hmr2 : (m : ℝ) ≤ 2 * M := by exact_mod_cast hm2
    have hMpos : (0 : ℝ) < M := by linarith
    -- the log-frequency difference is at most `log 2 ≤ 1` in absolute value
    have hdiff : (Real.log n - Real.log m) ^ 2 ≤ 1 := by
      have h1 : Real.log n - Real.log m ≤ Real.log (2 * M) - Real.log M := by
        have ha : Real.log n ≤ Real.log (2 * M) :=
          Real.log_le_log (by linarith) hnr2
        have hb : Real.log M ≤ Real.log m := Real.log_le_log hMpos hmr
        linarith
      have h2 : Real.log M - Real.log (2 * M) ≤ Real.log n - Real.log m := by
        have ha : Real.log M ≤ Real.log n := Real.log_le_log hMpos hnr
        have hb : Real.log m ≤ Real.log (2 * M) :=
          Real.log_le_log (by linarith) hmr2
        linarith
      have hlog2 : Real.log (2 * M) - Real.log M = Real.log 2 := by
        rw [Real.log_mul (by norm_num) (by positivity)]
        ring
      have hl2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
        linarith
      have hl2pos : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      rw [hlog2] at h1
      have h2' : -Real.log 2 ≤ Real.log n - Real.log m := by
        rw [← neg_sub, hlog2] at h2
        linarith
      nlinarith [h1, h2', hl2, hl2pos]
    -- the coefficients are at most `log 2M`
    have hLn : ArithmeticFunction.vonMangoldt n ≤ Real.log (2 * M) := by
      refine le_trans ArithmeticFunction.vonMangoldt_le_log ?_
      exact Real.log_le_log (by linarith) hnr2
    have hLm : ArithmeticFunction.vonMangoldt m ≤ Real.log (2 * M) := by
      refine le_trans ArithmeticFunction.vonMangoldt_le_log ?_
      exact Real.log_le_log (by linarith) hmr2
    have hLn0 : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hLm0 : 0 ≤ ArithmeticFunction.vonMangoldt m := ArithmeticFunction.vonMangoldt_nonneg
    have hsq0 : 0 ≤ (Real.log n - Real.log m) ^ 2 := sq_nonneg _
    have hprod : ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m
        ≤ Real.log (2 * M) ^ 2 := by
      have h := mul_le_mul hLn hLm hLm0 hlogM
      nlinarith [h]
    have hfin := mul_le_mul hprod hdiff hsq0 (sq_nonneg (Real.log (2 * M)))
    linarith [hfin]
  have hcard : (Finset.Icc M (2 * M)).card = M + 1 := by
    rw [Nat.card_Icc]
    omega
  calc ∑ n ∈ Finset.Icc M (2 * M), ∑ m ∈ Finset.Icc M (2 * M),
        ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt m
          * (Real.log n - Real.log m) ^ 2
      ≤ ∑ _n ∈ Finset.Icc M (2 * M), ∑ _m ∈ Finset.Icc M (2 * M), Real.log (2 * M) ^ 2 :=
        Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => hterm n hn m hm
    _ = Real.log (2 * M) ^ 2 * (M + 1) ^ 2 := by
        simp [Finset.sum_const, hcard]
        ring

end RiemannAnalytic
