/-
**The exact short-window second moment of a Dirichlet polynomial.**

Lane B needs an arithmetic input on a *short* window: a bound for the mean
square of a Dirichlet polynomial over an interval of length `H` much smaller
than the ambient height.  Every treatment of that question starts from one
elementary identity, and this file proves it from scratch, with no analytic
number theory assumed.

For `D_a,N(t) = ∑_{1 ≤ n ≤ N} a_n e^{-i t log n}` and a window `[0, H]`:

* `integral_expWindow` — `∫₀^H e^{iλt} dt = expWindow H λ`, equal to `H` on the
  diagonal `λ = 0` and to `(e^{iλH} − 1)/(iλ)` otherwise;
* `dirichletPoly_secondMoment_eq` — the exact expansion

      `∫₀^H |D(t)|² dt = ∑_{m,n} a_m conj(a_n) · expWindow H (log n − log m)`;

* `norm_expWindow_le` — off the diagonal `‖expWindow H λ‖ ≤ 2/|λ|`, uniformly in
  the window length `H`;
* `dirichletPoly_secondMoment_le` — hence the classical short-window bound

      `∫₀^H |D(t)|² dt ≤ H ∑_n |a_n|² + ∑_{m ≠ n} 2|a_m||a_n| / |log(n/m)|`.

The point for the programme is visible in the last two statements together: the
diagonal contributes exactly `H · ∑|a_n|²`, while the off-diagonal bound is
**independent of `H`**.  Shortening the window therefore shrinks the main term
and leaves the classical error term untouched — in the language of
`ShortWindowPrimeTarget.lean`, the classical route supplies cancellation
exponent `θ = 0` in the window height, whereas the local exterior-area target
needs `θ > 2`.  Any usable short-interval input must beat this expansion, not
merely invoke it.

Nothing here refers to `ζ`; `a` is an arbitrary finite coefficient sequence.
-/
import Mathlib

namespace RiemannAnalytic

open Complex Finset intervalIntegral MeasureTheory

/-! ### The window integral of a pure frequency -/

/-- `∫₀^H e^{iλt} dt`, in closed form. -/
noncomputable def expWindow (H lam : ℝ) : ℂ :=
  if lam = 0 then (H : ℂ) else (Complex.exp (Complex.I * (lam : ℂ) * (H : ℂ)) - 1)
    / (Complex.I * (lam : ℂ))

theorem integral_expWindow (H lam : ℝ) :
    (∫ t in (0 : ℝ)..H, Complex.exp (Complex.I * (lam : ℂ) * (t : ℂ))) = expWindow H lam := by
  unfold expWindow
  by_cases hlam : lam = 0
  · subst hlam
    simp
  · have hc : Complex.I * (lam : ℂ) ≠ 0 := by
      simp [Complex.I_ne_zero, hlam]
    rw [if_neg hlam]
    have := integral_exp_mul_complex (a := (0 : ℝ)) (b := H) (c := Complex.I * (lam : ℂ)) hc
    simpa using this

/-- Off the diagonal the window integral is bounded by `2/|λ|`, **uniformly in
the window length `H`**. -/
theorem norm_expWindow_le {H lam : ℝ} (hlam : lam ≠ 0) : ‖expWindow H lam‖ ≤ 2 / |lam| := by
  unfold expWindow
  rw [if_neg hlam, norm_div]
  have hnum : ‖Complex.exp (Complex.I * (lam : ℂ) * (H : ℂ)) - 1‖ ≤ 2 := by
    have habs : ‖Complex.exp (Complex.I * (lam : ℂ) * (H : ℂ))‖ = 1 := by
      have : Complex.I * (lam : ℂ) * (H : ℂ) = ((lam * H : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    calc ‖Complex.exp (Complex.I * (lam : ℂ) * (H : ℂ)) - 1‖
        ≤ ‖Complex.exp (Complex.I * (lam : ℂ) * (H : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [habs]; norm_num
  have hden : ‖Complex.I * (lam : ℂ)‖ = |lam| := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hden]
  have habspos : (0 : ℝ) < |lam| := abs_pos.2 hlam
  gcongr

/-! ### The Dirichlet polynomial and its short-window second moment -/

/-- The Dirichlet polynomial `∑_{1 ≤ n ≤ N} a_n n^{-it}`. -/
noncomputable def dirichletPoly (a : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, a n * Complex.exp (-(Complex.I * (Real.log n : ℂ) * (t : ℂ)))

theorem dirichletPoly_continuous (a : ℕ → ℂ) (N : ℕ) : Continuous (dirichletPoly a N) := by
  unfold dirichletPoly
  refine continuous_finset_sum _ fun n _ => ?_
  fun_prop

/-- The conjugate of a Dirichlet polynomial flips the sign of the frequency. -/
theorem conj_dirichletPoly (a : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    (starRingEnd ℂ) (dirichletPoly a N t)
      = ∑ n ∈ Finset.Icc 1 N,
          (starRingEnd ℂ) (a n) * Complex.exp (Complex.I * (Real.log n : ℂ) * (t : ℂ)) := by
  unfold dirichletPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  congr 1
  rw [map_neg, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
  ring_nf

/-- **The exact short-window second moment.**  Expanding the square and
integrating each frequency separately:

    `∫₀^H |D(t)|² dt = ∑_{m,n} a_m conj(a_n) · expWindow H (log n − log m)`. -/
theorem dirichletPoly_secondMoment_eq (a : ℕ → ℂ) (N : ℕ) (H : ℝ) :
    ((∫ t in (0 : ℝ)..H, ‖dirichletPoly a N t‖ ^ 2 : ℝ) : ℂ)
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          a m * (starRingEnd ℂ) (a n) * expWindow H (Real.log n - Real.log m) := by
  classical
  have hpt : ∀ t : ℝ, ((‖dirichletPoly a N t‖ ^ 2 : ℝ) : ℂ)
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          a m * (starRingEnd ℂ) (a n)
            * Complex.exp (Complex.I * ((Real.log n - Real.log m : ℝ) : ℂ) * (t : ℂ)) := by
    intro t
    have hmul : ((‖dirichletPoly a N t‖ ^ 2 : ℝ) : ℂ)
        = dirichletPoly a N t * (starRingEnd ℂ) (dirichletPoly a N t) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hmul, conj_dirichletPoly a N t]
    unfold dirichletPoly
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    have hexp : Complex.exp (-(Complex.I * (Real.log m : ℝ) * (t : ℝ)))
        * Complex.exp (Complex.I * (Real.log n : ℝ) * (t : ℝ))
        = Complex.exp (Complex.I * ((Real.log n - Real.log m : ℝ) : ℂ) * (t : ℝ)) := by
      rw [← Complex.exp_add]
      push_cast
      ring_nf
    calc a m * Complex.exp (-(Complex.I * (Real.log m : ℝ) * (t : ℝ)))
          * ((starRingEnd ℂ) (a n) * Complex.exp (Complex.I * (Real.log n : ℝ) * (t : ℝ)))
        = a m * (starRingEnd ℂ) (a n)
            * (Complex.exp (-(Complex.I * (Real.log m : ℝ) * (t : ℝ)))
              * Complex.exp (Complex.I * (Real.log n : ℝ) * (t : ℝ))) := by ring
      _ = a m * (starRingEnd ℂ) (a n)
            * Complex.exp (Complex.I * ((Real.log n - Real.log m : ℝ) : ℂ) * (t : ℝ)) := by
          rw [hexp]
  have hint : (∫ t in (0 : ℝ)..H, ((‖dirichletPoly a N t‖ ^ 2 : ℝ) : ℂ))
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          a m * (starRingEnd ℂ) (a n) * expWindow H (Real.log n - Real.log m) := by
    rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        a m * (starRingEnd ℂ) (a n)
          * Complex.exp (Complex.I * ((Real.log n - Real.log m : ℝ) : ℂ) * (t : ℂ)))
      (fun t _ => hpt t)]
    rw [intervalIntegral.integral_finset_sum]
    · refine Finset.sum_congr rfl fun m _ => ?_
      rw [intervalIntegral.integral_finset_sum]
      · refine Finset.sum_congr rfl fun n _ => ?_
        rw [intervalIntegral.integral_const_mul, integral_expWindow]
      · intro n _
        apply Continuous.intervalIntegrable
        fun_prop
    · intro m _
      apply Continuous.intervalIntegrable
      refine continuous_finset_sum _ fun n _ => ?_
      fun_prop
  rw [← hint, intervalIntegral.integral_ofReal]

/-! ### The classical short-window bound -/

/-- **The classical short-window mean-value bound.**  With the diagonal
contributing `H ∑ |a_n|²` and each off-diagonal frequency bounded by `2/|λ|`
*independently of the window length*:

    `∫₀^H |D(t)|² dt ≤ H ∑_n |a_n|² + ∑_{m ≠ n} 2|a_m||a_n| / |log n − log m|`.

Shortening the window shrinks only the first term. -/
theorem dirichletPoly_secondMoment_le (a : ℕ → ℂ) (N : ℕ) {H : ℝ} (hH : 0 ≤ H) :
    (∫ t in (0 : ℝ)..H, ‖dirichletPoly a N t‖ ^ 2)
      ≤ H * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * ‖a m‖ * ‖a n‖ / |Real.log n - Real.log m| := by
  classical
  set F : ℕ → ℕ → ℂ := fun m n =>
    a m * (starRingEnd ℂ) (a n) * expWindow H (Real.log n - Real.log m) with hF
  have heq := dirichletPoly_secondMoment_eq a N H
  have hle : (∫ t in (0 : ℝ)..H, ‖dirichletPoly a N t‖ ^ 2)
      ≤ ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, F m n‖ := by
    have h1 : ‖((∫ t in (0 : ℝ)..H, ‖dirichletPoly a N t‖ ^ 2 : ℝ) : ℂ)‖
        = |∫ t in (0 : ℝ)..H, ‖dirichletPoly a N t‖ ^ 2| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    rw [← heq, h1]
    exact le_abs_self _
  -- bound the double sum termwise
  have hsplit : ∀ m ∈ Finset.Icc 1 N,
      ‖∑ n ∈ Finset.Icc 1 N, F m n‖
        ≤ H * ‖a m‖ ^ 2
          + ∑ n ∈ (Finset.Icc 1 N).erase m, 2 * ‖a m‖ * ‖a n‖ / |Real.log n - Real.log m| := by
    intro m hm
    have hdecomp : ∑ n ∈ Finset.Icc 1 N, F m n
        = F m m + ∑ n ∈ (Finset.Icc 1 N).erase m, F m n :=
      (Finset.add_sum_erase _ (fun n => F m n) hm).symm
    have hdiag : ‖F m m‖ = H * ‖a m‖ ^ 2 := by
      rw [hF]
      simp only [sub_self]
      rw [expWindow, if_pos rfl, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hH, RCLike.norm_conj]
      ring
    have hoff : ∀ n ∈ (Finset.Icc 1 N).erase m,
        ‖F m n‖ ≤ 2 * ‖a m‖ * ‖a n‖ / |Real.log n - Real.log m| := by
      intro n hn
      obtain ⟨hnm, hnI⟩ := Finset.mem_erase.1 hn
      have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hm).1
      have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hnI).1
      have hlam : Real.log n - Real.log m ≠ 0 := by
        have hmr : (0 : ℝ) < m := by exact_mod_cast hm1
        have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
        have hne : (n : ℝ) ≠ (m : ℝ) := by exact_mod_cast hnm
        have : Real.log n ≠ Real.log m := fun hcon =>
          hne (Real.log_injOn_pos (Set.mem_Ioi.2 hnr) (Set.mem_Ioi.2 hmr) hcon)
        exact sub_ne_zero.2 this
      have hb := norm_expWindow_le (H := H) hlam
      rw [hF]
      simp only [norm_mul, RCLike.norm_conj]
      have hnn : (0 : ℝ) ≤ ‖a m‖ * ‖a n‖ := by positivity
      calc ‖a m‖ * ‖a n‖ * ‖expWindow H (Real.log n - Real.log m)‖
          ≤ ‖a m‖ * ‖a n‖ * (2 / |Real.log n - Real.log m|) := by
            exact mul_le_mul_of_nonneg_left hb hnn
        _ = 2 * ‖a m‖ * ‖a n‖ / |Real.log n - Real.log m| := by ring
    calc ‖∑ n ∈ Finset.Icc 1 N, F m n‖
        = ‖F m m + ∑ n ∈ (Finset.Icc 1 N).erase m, F m n‖ := by rw [hdecomp]
      _ ≤ ‖F m m‖ + ‖∑ n ∈ (Finset.Icc 1 N).erase m, F m n‖ := norm_add_le _ _
      _ ≤ H * ‖a m‖ ^ 2
            + ∑ n ∈ (Finset.Icc 1 N).erase m, 2 * ‖a m‖ * ‖a n‖ / |Real.log n - Real.log m| := by
          have := norm_sum_le ((Finset.Icc 1 N).erase m) (fun n => F m n)
          have h2 : ∑ n ∈ (Finset.Icc 1 N).erase m, ‖F m n‖
              ≤ ∑ n ∈ (Finset.Icc 1 N).erase m,
                  2 * ‖a m‖ * ‖a n‖ / |Real.log n - Real.log m| :=
            Finset.sum_le_sum hoff
          rw [hdiag]
          linarith
  have htotal : ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, F m n‖
      ≤ ∑ m ∈ Finset.Icc 1 N, (H * ‖a m‖ ^ 2
          + ∑ n ∈ (Finset.Icc 1 N).erase m,
              2 * ‖a m‖ * ‖a n‖ / |Real.log n - Real.log m|) := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum hsplit)
  have hrearrange : ∑ m ∈ Finset.Icc 1 N, (H * ‖a m‖ ^ 2
      + ∑ n ∈ (Finset.Icc 1 N).erase m, 2 * ‖a m‖ * ‖a n‖ / |Real.log n - Real.log m|)
      = H * ∑ n ∈ Finset.Icc 1 N, ‖a n‖ ^ 2
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
            2 * ‖a m‖ * ‖a n‖ / |Real.log n - Real.log m| := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  linarith [hle, htotal, hrearrange.le, hrearrange.ge]

end RiemannAnalytic
