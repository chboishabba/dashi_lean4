/-
**Q8.2 / Q8.3 — the diagonal of the imaginary (transverse) projection, computed.**

The anchored observable of the programme is built from the *transverse*
coordinate `b = Im Φ`, and the hope recorded in the G8 plan was that the
conjugate algebra

    `(Im z)² = (‖z‖² − Re z²)/2`

might annihilate the diagonal that generic mean-square theory produces.  This
file settles that question for the natural Dirichlet-polynomial model, by
computing the diagonal exactly rather than estimating it.

* `imSq_eq` — the conjugate identity above, in the form actually used;
* `dirichletPoly_sqIntegral_eq` — the exact expansion of the *unconjugated*
  square `∫₀^H D(t)² dt = ∑_{m,n} a_m a_n · expWindow H (−(log m + log n))`.
  Its frequencies are `log(mn)`, which vanish only at `m = n = 1`, so this
  second piece carries **no** diagonal once `a₁ = 0` (as for a von Mangoldt
  weight);
* `im_secondMoment_eq` — hence the exact identity
  `∫₀^H (Im D)² = ½(∫₀^H |D|² − Re ∫₀^H D²)`;
* `im_secondMoment_sub_half_diagonal_le` — **the answer**: with `a₁ = 0`,

      `|∫₀^H (Im D)² − ½H ∑_n |a_n|²| ≤ ½(E₁ + E₂)`,

  where `E₁, E₂` are the two off-diagonal sums, both **independent of the window
  length `H`**.

So the transverse projection is outcome **(B)-in-name-only**: it multiplies the
diagonal by `1/2` and leaves it otherwise intact.  It does **not** cancel it.
Combined with `ShiftProjector.lean` — where the annihilating projector `P(1)=0`
does remove the zero-frequency mode exactly, but damps the rest only by
`(|s| log N)²`, a constant at the source scaling — the conclusion for the
programme is that neither the imaginary projection nor a fixed finite shift
projector supplies the strict gain `δ = θ − 2 > 0` that G7 showed is required.

Nothing here refers to `ζ`; `a` is an arbitrary finite coefficient sequence.
-/
import RiemannAnalytic.ShiftProjector

namespace RiemannAnalytic

open Complex Finset intervalIntegral MeasureTheory

/-- `(Im z)² = (‖z‖² − Re z²)/2`: the conjugate algebra of the transverse
coordinate. -/
theorem imSq_eq (z : ℂ) : z.im ^ 2 = (‖z‖ ^ 2 - (z ^ 2).re) / 2 := by
  have hnorm : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hsq : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    rw [pow_two, Complex.mul_re]
    ring
  rw [hnorm, hsq]
  ring

/-- **The exact expansion of the unconjugated square.**  Its frequencies are
`log(mn)`, so the only zero frequency is `m = n = 1`. -/
theorem dirichletPoly_sqIntegral_eq (a : ℕ → ℂ) (N : ℕ) (H : ℝ) :
    (∫ t in (0 : ℝ)..H, (dirichletPoly a N t) ^ 2)
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          a m * a n * expWindow H (-(Real.log m + Real.log n)) := by
  classical
  have hpt : ∀ t : ℝ, (dirichletPoly a N t) ^ 2
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
          a m * a n
            * Complex.exp (Complex.I * ((-(Real.log m + Real.log n) : ℝ) : ℂ) * (t : ℂ)) := by
    intro t
    unfold dirichletPoly
    rw [pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    have hexp : Complex.exp (-(Complex.I * (Real.log m : ℂ) * (t : ℂ)))
        * Complex.exp (-(Complex.I * (Real.log n : ℂ) * (t : ℂ)))
        = Complex.exp (Complex.I * ((-(Real.log m + Real.log n) : ℝ) : ℂ) * (t : ℂ)) := by
      rw [← Complex.exp_add]
      push_cast
      ring_nf
    calc a m * Complex.exp (-(Complex.I * (Real.log m : ℂ) * (t : ℂ)))
          * (a n * Complex.exp (-(Complex.I * (Real.log n : ℂ) * (t : ℂ))))
        = a m * a n * (Complex.exp (-(Complex.I * (Real.log m : ℂ) * (t : ℂ)))
            * Complex.exp (-(Complex.I * (Real.log n : ℂ) * (t : ℂ)))) := by ring
      _ = a m * a n
            * Complex.exp (Complex.I * ((-(Real.log m + Real.log n) : ℝ) : ℂ) * (t : ℂ)) := by
          rw [hexp]
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
    ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
      a m * a n * Complex.exp (Complex.I * ((-(Real.log m + Real.log n) : ℝ) : ℂ) * (t : ℂ)))
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

/-- **The transverse second moment, exactly.**
`∫₀^H (Im D)² = ½(∫₀^H |D|² − Re ∫₀^H D²)`. -/
theorem im_secondMoment_eq (a : ℕ → ℂ) (N : ℕ) (H : ℝ) :
    (∫ t in (0 : ℝ)..H, ((dirichletPoly a N t).im) ^ 2)
      = ((∫ t in (0 : ℝ)..H, ‖dirichletPoly a N t‖ ^ 2)
          - (∫ t in (0 : ℝ)..H, (dirichletPoly a N t) ^ 2).re) / 2 := by
  have hc : Continuous (dirichletPoly a N) := dirichletPoly_continuous a N
  have hre : (∫ t in (0 : ℝ)..H, ((dirichletPoly a N t) ^ 2).re)
      = (∫ t in (0 : ℝ)..H, (dirichletPoly a N t) ^ 2).re := by
    have := ContinuousLinearMap.intervalIntegral_comp_comm (μ := volume) Complex.reCLM
      ((hc.pow 2).intervalIntegrable (μ := volume) 0 H)
    simpa using this
  have hcongr : (∫ t in (0 : ℝ)..H, ((dirichletPoly a N t).im) ^ 2)
      = ∫ t in (0 : ℝ)..H,
          (‖dirichletPoly a N t‖ ^ 2 - ((dirichletPoly a N t) ^ 2).re) / 2 :=
    intervalIntegral.integral_congr fun t _ => imSq_eq _
  rw [hcongr, intervalIntegral.integral_div,
    intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) 0 H)
      (Continuous.intervalIntegrable (by fun_prop) 0 H), hre]

/-! ### The diagonal of the transverse projection -/

/-- The off-diagonal sum of the conjugated square. -/
noncomputable def offDiagSum (a : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m,
    2 * ‖a m‖ * ‖a n‖ / |Real.log n - Real.log m|

/-- The total mass of the unconjugated square. -/
noncomputable def sqSum (a : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
    2 * ‖a m‖ * ‖a n‖ / (Real.log m + Real.log n)

theorem offDiagSum_nonneg (a : ℕ → ℂ) (N : ℕ) : 0 ≤ offDiagSum a N :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem sqSum_nonneg (a : ℕ → ℂ) (N : ℕ) : 0 ≤ sqSum a N := by
  refine Finset.sum_nonneg fun m hm => Finset.sum_nonneg fun n hn => ?_
  rw [Finset.mem_Icc] at hm hn
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
  have := Real.log_nonneg hm1
  have := Real.log_nonneg hn1
  positivity

/-- The conjugated square, with its diagonal split off. -/
theorem secondMoment_sub_diagonal_le (a : ℕ → ℂ) (N : ℕ) (H : ℝ) :
    |(∫ t in (0 : ℝ)..H, ‖dirichletPoly a N t‖ ^ 2) - H * diagonalMass a N|
      ≤ offDiagSum a N := by
  classical
  have heq := dirichletPoly_secondMoment_eq a N H
  set F : ℕ → ℕ → ℂ := fun m n =>
    a m * (starRingEnd ℂ) (a n) * expWindow H (Real.log n - Real.log m) with hF
  have hsplit : ∀ m ∈ Finset.Icc 1 N,
      ∑ n ∈ Finset.Icc 1 N, F m n
        = ((H * ‖a m‖ ^ 2 : ℝ) : ℂ) + ∑ n ∈ (Finset.Icc 1 N).erase m, F m n := by
    intro m hm
    rw [← Finset.add_sum_erase _ (fun n => F m n) hm]
    congr 1
    rw [hF]
    simp only [sub_self]
    rw [expWindow, if_pos rfl, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hsum : ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N, F m n
      = ((H * diagonalMass a N : ℝ) : ℂ)
        + ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m, F m n := by
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    congr 1
    unfold diagonalMass
    push_cast
    rw [Finset.mul_sum]
  have hval : ((∫ t in (0 : ℝ)..H, ‖dirichletPoly a N t‖ ^ 2 : ℝ) : ℂ)
      - ((H * diagonalMass a N : ℝ) : ℂ)
      = ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m, F m n := by
    rw [heq, hsum]
    ring
  have hnorm : ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m, F m n‖
      ≤ offDiagSum a N := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m hmem => ?_)
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n hn => ?_)
    have hne : n ≠ m := Finset.ne_of_mem_erase hn
    have hlogne : Real.log n - Real.log m ≠ 0 := by
      intro hzero
      have hlog : Real.log n = Real.log m := by linarith
      have hm1 : 1 ≤ m := (Finset.mem_Icc.1 hmem).1
      have hn1 : 1 ≤ n := (Finset.mem_Icc.1 (Finset.mem_of_mem_erase hn)).1
      have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hm1
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn1
      have : (n : ℝ) = (m : ℝ) := by
        have := Real.log_injOn_pos (Set.mem_Ioi.2 hnpos) (Set.mem_Ioi.2 hmpos) hlog
        exact this
      exact hne (by exact_mod_cast this)
    rw [hF, norm_mul, norm_mul, RCLike.norm_conj]
    have := norm_expWindow_le (H := H) hlogne
    calc ‖a m‖ * ‖a n‖ * ‖expWindow H (Real.log n - Real.log m)‖
        ≤ ‖a m‖ * ‖a n‖ * (2 / |Real.log n - Real.log m|) := by
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * ‖a m‖ * ‖a n‖ / |Real.log n - Real.log m| := by ring
  have habs : |(∫ t in (0 : ℝ)..H, ‖dirichletPoly a N t‖ ^ 2) - H * diagonalMass a N|
      = ‖∑ m ∈ Finset.Icc 1 N, ∑ n ∈ (Finset.Icc 1 N).erase m, F m n‖ := by
    rw [← hval]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [habs]
  exact hnorm

/-- The unconjugated square carries no diagonal once `a₁ = 0`. -/
theorem sqIntegral_norm_le (a : ℕ → ℂ) (N : ℕ) (H : ℝ) (ha1 : a 1 = 0) :
    ‖∫ t in (0 : ℝ)..H, (dirichletPoly a N t) ^ 2‖ ≤ sqSum a N := by
  classical
  rw [dirichletPoly_sqIntegral_eq]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m hm => ?_)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n hn => ?_)
  rw [Finset.mem_Icc] at hm hn
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.1
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
  have hlm : 0 ≤ Real.log m := Real.log_nonneg hm1
  have hln : 0 ≤ Real.log n := Real.log_nonneg hn1
  by_cases hone : m = 1 ∧ n = 1
  · obtain ⟨hm', hn'⟩ := hone
    subst hm'
    subst hn'
    rw [ha1]
    simp
  · have hpos : 0 < Real.log m + Real.log n := by
      rcases not_and_or.1 hone with hm2 | hn2
      · have : 2 ≤ m := by omega
        have h2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast this
        have : 0 < Real.log m := Real.log_pos (by linarith)
        linarith
      · have : 2 ≤ n := by omega
        have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
        have : 0 < Real.log n := Real.log_pos (by linarith)
        linarith
    have hne : -(Real.log m + Real.log n) ≠ 0 := by intro h; linarith [neg_eq_zero.1 h]
    have hbd := norm_expWindow_le (H := H) hne
    rw [abs_of_nonpos (by linarith : -(Real.log m + Real.log n) ≤ 0), neg_neg] at hbd
    rw [norm_mul, norm_mul]
    calc ‖a m‖ * ‖a n‖ * ‖expWindow H (-(Real.log m + Real.log n))‖
        ≤ ‖a m‖ * ‖a n‖ * (2 / (Real.log m + Real.log n)) :=
          mul_le_mul_of_nonneg_left hbd (by positivity)
      _ = 2 * ‖a m‖ * ‖a n‖ / (Real.log m + Real.log n) := by ring

/-- **The transverse projection retains exactly half the diagonal.**

For any finite coefficient sequence with `a₁ = 0`,

    `|∫₀^H (Im D)² − ½H ∑_n |a_n|²| ≤ ½ (offDiagSum + sqSum)`,

with both error sums **independent of the window length `H`**.  So the passage
to the imaginary part does not cancel the diagonal produced by generic
mean-square theory: it halves it.  This answers the G8 question about the
transverse projection in the negative, by exact computation rather than by
estimate. -/
theorem im_secondMoment_sub_half_diagonal_le (a : ℕ → ℂ) (N : ℕ) (H : ℝ) (ha1 : a 1 = 0) :
    |(∫ t in (0 : ℝ)..H, ((dirichletPoly a N t).im) ^ 2) - 1 / 2 * (H * diagonalMass a N)|
      ≤ 1 / 2 * (offDiagSum a N + sqSum a N) := by
  rw [im_secondMoment_eq]
  have h1 := secondMoment_sub_diagonal_le a N H
  have h2 := sqIntegral_norm_le a N H ha1
  have h2' : |(∫ t in (0 : ℝ)..H, (dirichletPoly a N t) ^ 2).re| ≤ sqSum a N :=
    le_trans (Complex.abs_re_le_norm _) h2
  have hkey : ((∫ t in (0 : ℝ)..H, ‖dirichletPoly a N t‖ ^ 2)
      - (∫ t in (0 : ℝ)..H, (dirichletPoly a N t) ^ 2).re) / 2 - 1 / 2 * (H * diagonalMass a N)
      = 1 / 2 * (((∫ t in (0 : ℝ)..H, ‖dirichletPoly a N t‖ ^ 2) - H * diagonalMass a N)
          - (∫ t in (0 : ℝ)..H, (dirichletPoly a N t) ^ 2).re) := by ring
  rw [hkey, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have := abs_sub ((∫ t in (0 : ℝ)..H, ‖dirichletPoly a N t‖ ^ 2) - H * diagonalMass a N)
    ((∫ t in (0 : ℝ)..H, (dirichletPoly a N t) ^ 2).re)
  have habs : |((∫ t in (0 : ℝ)..H, ‖dirichletPoly a N t‖ ^ 2) - H * diagonalMass a N)
      - (∫ t in (0 : ℝ)..H, (dirichletPoly a N t) ^ 2).re|
      ≤ offDiagSum a N + sqSum a N := by
    refine le_trans (abs_sub _ _) ?_
    linarith
  linarith

end RiemannAnalytic
