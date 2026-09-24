/-
**G10 — the compensated anchored observable, and the first `α²`-carrying
prime-side bound.**

Two facts now constrain the programme from opposite sides.

* `RelativeContraction.absolute_budget_insufficient`: an `o(L⁶)` budget can
  never force `α = 0`.  The endgame needs a bound proportional to `α²`.
* `AnchoredPrimeExpansion.anchoredPrime_no_alpha_factor_of_positive_baseline`:
  the **raw** anchored prime observable is positive at `α = 0`, so it can never
  satisfy such a bound.

The only way out is the compensated (baseline-subtracted) observable

    `𝒟(α) = 𝒜(α) − 𝒜(0)`,

which is exactly the object the gauge analysis of `PhaseGauge` also pointed to.
This file proves that the compensated observable *does* carry the factor `α²`,
for the weight family the functional equation actually produces.

The prime-side amplitude mass of a target displaced by `α` from the critical
line is, after pairing `ρ` with `1 − ρ̄`, symmetric in `α`:

    `w_n(α) = w_n · cosh(2αλ_n)`,   `λ_n = log n`.

For that family we prove, with explicit constants and no asymptotics:

    `𝒟(α) ≤ K·α²·𝒜_0`,  `K = 2κ + κ²A²`,  `κ = 2Λ²e^{2AΛ}`,

valid for `|α| ≤ A` and log-frequencies bounded by `Λ`
(`compensatedMinor_cosh_le`).  Combined with the G9 log-variance ledger this is
a bound of the shape `𝒟 ≤ K·α²·s²·Var`, i.e. the `α²`-carrying prime bound the
relative endgame consumes — modulo instantiating `Λ`, `A` and the amplitude mass
at the literal zeta source, which is **not** done here.

Nothing in this file refers to `ζ`, and nothing below is assumed elsewhere.
-/
import RiemannAnalytic.AnchoredPrimeExpansion

namespace RiemannAnalytic

open Finset

variable {d : ℕ}

/-! ### Elementary hyperbolic estimates -/

/-- `sinh y ≤ y·e^y` for every real `y`. -/
theorem sinh_le_mul_exp (y : ℝ) : Real.sinh y ≤ y * Real.exp y := by
  rw [Real.sinh_eq]
  have h2 : (1 : ℝ) - 2 * y ≤ Real.exp (-(2 * y)) := by
    have := Real.add_one_le_exp (-(2 * y)); linarith
  have hp : 0 < Real.exp y := Real.exp_pos y
  have hrw : Real.exp (-y) = Real.exp y * Real.exp (-(2 * y)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hrw]; nlinarith [h2, hp]

/-- A quantitative quadratic bound for `cosh` on a bounded interval:
`cosh x − 1 ≤ (x²/2)e^A` whenever `|x| ≤ A`. -/
theorem cosh_sub_one_le {A x : ℝ} (hx : |x| ≤ A) :
    Real.cosh x - 1 ≤ x ^ 2 / 2 * Real.exp A := by
  have hkey : Real.cosh x - 1 = 2 * Real.sinh (x / 2) ^ 2 := by
    have h := Real.cosh_two_mul (x / 2)
    have hc := Real.cosh_sq (x / 2)
    rw [show 2 * (x / 2) = x by ring] at h
    nlinarith [h, hc]
  have habs : |Real.sinh (x / 2)| = Real.sinh |x / 2| := Real.abs_sinh _
  have hb : Real.sinh |x / 2| ≤ |x / 2| * Real.exp |x / 2| := sinh_le_mul_exp _
  have hpos : 0 ≤ Real.sinh |x / 2| := Real.sinh_nonneg_iff.mpr (abs_nonneg _)
  have hxx : |x / 2| = |x| / 2 := by rw [abs_div]; simp
  have hexpsq : Real.exp |x / 2| ^ 2 = Real.exp |x| := by
    rw [pow_two, ← Real.exp_add, hxx]; ring_nf
  have hsqbound : Real.sinh |x / 2| ^ 2 ≤ x ^ 2 / 4 * Real.exp |x| := by
    have h1 : Real.sinh |x / 2| ^ 2 ≤ (|x / 2| * Real.exp |x / 2|) ^ 2 := by
      nlinarith [hb, hpos]
    have h2 : (|x / 2| * Real.exp |x / 2|) ^ 2 = x ^ 2 / 4 * Real.exp |x| := by
      rw [mul_pow, hexpsq, hxx, div_pow, sq_abs]; ring
    linarith [h1, h2.le, h2.ge]
  have hsq : Real.sinh (x / 2) ^ 2 = Real.sinh |x / 2| ^ 2 := by rw [← habs, sq_abs]
  have hexp : Real.exp |x| ≤ Real.exp A := Real.exp_le_exp.mpr hx
  have hx2 : (0 : ℝ) ≤ x ^ 2 / 4 := by positivity
  rw [hkey, hsq]
  nlinarith [hsqbound, hexp, hx2]

/-- A product of two factors, each `≤ 1 + κα²` and the second `≥ 1`, exceeds `1`
by at most `(2κ + κ²A²)α²` when `α² ≤ A²`. -/
theorem prod_sub_one_le_quadratic {c₁ c₂ kappa alpha A : ℝ}
    (hc₂ : 1 ≤ c₂) (hk : 0 ≤ kappa)
    (h₁ : c₁ ≤ 1 + kappa * alpha ^ 2) (h₂ : c₂ ≤ 1 + kappa * alpha ^ 2)
    (hA : alpha ^ 2 ≤ A ^ 2) :
    c₁ * c₂ - 1 ≤ (2 * kappa + kappa ^ 2 * A ^ 2) * alpha ^ 2 := by
  have hsq : 0 ≤ alpha ^ 2 := sq_nonneg alpha
  have hb : 0 ≤ 1 + kappa * alpha ^ 2 := by positivity
  have step₁ : c₁ * c₂ ≤ (1 + kappa * alpha ^ 2) * c₂ :=
    mul_le_mul_of_nonneg_right h₁ (by linarith)
  have step₂ : (1 + kappa * alpha ^ 2) * c₂ ≤ (1 + kappa * alpha ^ 2) * (1 + kappa * alpha ^ 2) :=
    mul_le_mul_of_nonneg_left h₂ hb
  have hquad : (1 + kappa * alpha ^ 2) * (1 + kappa * alpha ^ 2) - 1
      = 2 * kappa * alpha ^ 2 + kappa ^ 2 * alpha ^ 2 * alpha ^ 2 := by ring
  have hlast : kappa ^ 2 * alpha ^ 2 * alpha ^ 2 ≤ kappa ^ 2 * A ^ 2 * alpha ^ 2 := by
    have : 0 ≤ kappa ^ 2 * alpha ^ 2 := by positivity
    nlinarith [hA, this]
  nlinarith [step₁, step₂, hquad.le, hquad.ge, hlast]

/-! ### The weight-level anchored observable -/

/-- The anchored observable written directly in terms of the amplitude weights:
`𝒜(w) = ∑_{n,m} w_n w_m (1 − cos(s(λ_n − λ_m)))`. -/
noncomputable def minorForm (w lam : Fin d → ℝ) (s : ℝ) : ℝ :=
  ∑ n, ∑ m, w n * w m * (1 - Real.cos (s * (lam n - lam m)))

/-- The exact anchored minor of a translated family is the weight-level form of
its amplitude weights. -/
theorem hermAnchorMinor_translate_eq_minorForm (a : Fin d → ℂ) (lam : Fin d → ℝ) (s : ℝ) :
    hermAnchorMinor (translateVec a lam 0) (translateVec a lam s)
      = minorForm (ampWeight a) lam s :=
  hermAnchorMinor_translate_eq a lam s

theorem minorForm_nonneg {w lam : Fin d → ℝ} (s : ℝ) (hw : ∀ n, 0 ≤ w n) :
    0 ≤ minorForm w lam s := by
  refine Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun m _ => ?_
  have hcos : 0 ≤ 1 - Real.cos (s * (lam n - lam m)) := by
    have := Real.cos_le_one (s * (lam n - lam m)); linarith
  exact mul_nonneg (mul_nonneg (hw n) (hw m)) hcos

/-- **The compensated (baseline-subtracted) observable** `𝒟(α) = 𝒜(α) − 𝒜(0)`. -/
noncomputable def compensatedMinor (W : ℝ → Fin d → ℝ) (lam : Fin d → ℝ)
    (s alpha : ℝ) : ℝ :=
  minorForm (W alpha) lam s - minorForm (W 0) lam s

/-- The compensated observable vanishes on the critical line by construction. -/
theorem compensatedMinor_zero (W : ℝ → Fin d → ℝ) (lam : Fin d → ℝ) (s : ℝ) :
    compensatedMinor W lam s 0 = 0 := by
  unfold compensatedMinor; ring

/-! ### The functional-equation weight family -/

/-- The prime-side amplitude mass of a target displaced by `α`, symmetrised by
the functional equation: `w_n(α) = w_n·cosh(2αλ_n)`. -/
noncomputable def coshWeight (w lam : Fin d → ℝ) (alpha : ℝ) : Fin d → ℝ :=
  fun n => w n * Real.cosh (2 * alpha * lam n)

@[simp] theorem coshWeight_zero (w lam : Fin d → ℝ) : coshWeight w lam 0 = w := by
  funext n; simp [coshWeight]

/-- **The `α²`-carrying compensated bound.**  For the functional-equation weight
family, with log-frequencies bounded by `Λ` and `|α| ≤ A`, the compensated
anchored observable is at most `K·α²` times the baseline observable, where
`κ = 2Λ²e^{2AΛ}` and `K = 2κ + κ²A²`.  In particular it vanishes to second order
on the critical line — the property the raw observable provably cannot have. -/
theorem compensatedMinor_cosh_le {w lam : Fin d → ℝ} {s alpha A Lam : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hLam : ∀ n, |lam n| ≤ Lam) (hLam0 : 0 ≤ Lam)
    (hA : |alpha| ≤ A) (hA0 : 0 ≤ A) :
    compensatedMinor (coshWeight w lam) lam s alpha
      ≤ (2 * (2 * Lam ^ 2 * Real.exp (2 * A * Lam))
          + (2 * Lam ^ 2 * Real.exp (2 * A * Lam)) ^ 2 * A ^ 2) * alpha ^ 2
        * minorForm w lam s := by
  set kappa : ℝ := 2 * Lam ^ 2 * Real.exp (2 * A * Lam) with hkappa
  set K : ℝ := 2 * kappa + kappa ^ 2 * A ^ 2 with hK
  have hkappa0 : 0 ≤ kappa := by
    have := Real.exp_pos (2 * A * Lam); positivity
  have halpha2 : alpha ^ 2 ≤ A ^ 2 := by
    have h := abs_nonneg alpha
    nlinarith [hA, h, sq_abs alpha]
  -- each cosh factor is between `1` and `1 + κα²`
  have hcosh : ∀ n, Real.cosh (2 * alpha * lam n) ≤ 1 + kappa * alpha ^ 2 := by
    intro n
    have hxb : |2 * alpha * lam n| ≤ 2 * A * Lam := by
      rw [abs_mul, abs_mul]
      have h1 : |(2 : ℝ)| = 2 := by norm_num
      rw [h1]
      have := hLam n
      have hprod : |alpha| * |lam n| ≤ A * Lam :=
        mul_le_mul hA this (abs_nonneg _) hA0
      linarith
    have := cosh_sub_one_le hxb
    have hsq : (2 * alpha * lam n) ^ 2 ≤ 4 * alpha ^ 2 * Lam ^ 2 := by
      have hl : lam n ^ 2 ≤ Lam ^ 2 := by
        have := hLam n
        nlinarith [abs_nonneg (lam n), sq_abs (lam n), hLam0]
      nlinarith [sq_nonneg alpha, hl]
    have hE : 0 < Real.exp (2 * A * Lam) := Real.exp_pos _
    nlinarith [this, hsq, hE]
  have hone : ∀ n, (1 : ℝ) ≤ Real.cosh (2 * alpha * lam n) := fun n => Real.one_le_cosh _
  -- termwise comparison
  have hterm : ∀ n m : Fin d,
      coshWeight w lam alpha n * coshWeight w lam alpha m *
          (1 - Real.cos (s * (lam n - lam m)))
        - w n * w m * (1 - Real.cos (s * (lam n - lam m)))
        ≤ K * alpha ^ 2 * (w n * w m * (1 - Real.cos (s * (lam n - lam m)))) := by
    intro n m
    have hcos : 0 ≤ 1 - Real.cos (s * (lam n - lam m)) := by
      have := Real.cos_le_one (s * (lam n - lam m)); linarith
    have hprod : Real.cosh (2 * alpha * lam n) * Real.cosh (2 * alpha * lam m) - 1
        ≤ K * alpha ^ 2 :=
      prod_sub_one_le_quadratic (hone m) hkappa0 (hcosh n) (hcosh m) halpha2
    have hww : 0 ≤ w n * w m := mul_nonneg (hw n) (hw m)
    have hexp : coshWeight w lam alpha n * coshWeight w lam alpha m
        = (w n * w m) * (Real.cosh (2 * alpha * lam n) * Real.cosh (2 * alpha * lam m)) := by
      unfold coshWeight; ring
    rw [hexp]
    nlinarith [mul_le_mul_of_nonneg_left hprod (mul_nonneg hww hcos)]
  -- sum the comparison
  have hsum : minorForm (coshWeight w lam alpha) lam s - minorForm w lam s
      ≤ K * alpha ^ 2 * minorForm w lam s := by
    unfold minorForm
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_le_sum fun m _ => hterm n m
  unfold compensatedMinor
  simpa [coshWeight_zero] using hsum

/-- **The usable regime, with a clean constant.**  The constant in
`compensatedMinor_cosh_le` grows like `e^{2AΛ}`: the same `cosh` blow-up that
closed the even-taper lane.  It is harmless exactly when the displacement range
and the log-frequency range are reciprocal, `A·Λ ≤ 1`, and then

    `𝒟(α) ≤ 8Λ²e⁴·α²·𝒜(0)`. -/
theorem compensatedMinor_cosh_le_of_reciprocal {w lam : Fin d → ℝ} {s alpha A Lam : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hLam : ∀ n, |lam n| ≤ Lam) (hLam0 : 0 ≤ Lam)
    (hA : |alpha| ≤ A) (hA0 : 0 ≤ A) (hAL : A * Lam ≤ 1) :
    compensatedMinor (coshWeight w lam) lam s alpha
      ≤ 8 * Lam ^ 2 * Real.exp 4 * alpha ^ 2 * minorForm w lam s := by
  have hbase := compensatedMinor_cosh_le (s := s) hw hLam hLam0 hA hA0
  have hexp2 : Real.exp (2 * A * Lam) ≤ Real.exp 2 :=
    Real.exp_le_exp.mpr (by nlinarith [hAL])
  have hexp0 : 0 < Real.exp (2 * A * Lam) := Real.exp_pos _
  have he24 : Real.exp 2 ≤ Real.exp 4 := Real.exp_le_exp.mpr (by norm_num)
  have hL2 : 0 ≤ Lam ^ 2 := sq_nonneg _
  have hkappa : 2 * Lam ^ 2 * Real.exp (2 * A * Lam) ≤ 2 * Lam ^ 2 * Real.exp 2 := by
    nlinarith [hexp2, hL2]
  have hAL2 : A ^ 2 * Lam ^ 2 ≤ 1 := by
    have hp : 0 ≤ A * Lam := mul_nonneg hA0 hLam0
    have heq : A ^ 2 * Lam ^ 2 = (A * Lam) ^ 2 := by ring
    rw [heq]
    nlinarith [hp, hAL]
  have hK : (2 * (2 * Lam ^ 2 * Real.exp (2 * A * Lam))
      + (2 * Lam ^ 2 * Real.exp (2 * A * Lam)) ^ 2 * A ^ 2)
      ≤ 8 * Lam ^ 2 * Real.exp 4 := by
    have hsq : (2 * Lam ^ 2 * Real.exp (2 * A * Lam)) ^ 2 * A ^ 2
        ≤ 4 * Lam ^ 2 * Real.exp 4 := by
      have h1 : (2 * Lam ^ 2 * Real.exp (2 * A * Lam)) ^ 2
          ≤ 4 * Lam ^ 4 * Real.exp 4 := by
        have hsqexp : Real.exp (2 * A * Lam) ^ 2 ≤ Real.exp 4 := by
          rw [pow_two, ← Real.exp_add]
          exact Real.exp_le_exp.mpr (by nlinarith [hAL])
        have heq : (2 * Lam ^ 2 * Real.exp (2 * A * Lam)) ^ 2
            = 4 * Lam ^ 4 * Real.exp (2 * A * Lam) ^ 2 := by ring
        rw [heq]
        have h4 : (0 : ℝ) ≤ 4 * Lam ^ 4 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hsqexp h4]
      have hA2 : 0 ≤ A ^ 2 := sq_nonneg _
      have hE4 : 0 < Real.exp 4 := Real.exp_pos _
      have hstep : (2 * Lam ^ 2 * Real.exp (2 * A * Lam)) ^ 2 * A ^ 2
          ≤ 4 * Lam ^ 4 * Real.exp 4 * A ^ 2 := mul_le_mul_of_nonneg_right h1 hA2
      have heq2 : 4 * Lam ^ 4 * Real.exp 4 * A ^ 2
          = (4 * Lam ^ 2 * Real.exp 4) * (A ^ 2 * Lam ^ 2) := by ring
      have hpos : (0 : ℝ) ≤ 4 * Lam ^ 2 * Real.exp 4 := by positivity
      have hfin : (4 * Lam ^ 2 * Real.exp 4) * (A ^ 2 * Lam ^ 2)
          ≤ (4 * Lam ^ 2 * Real.exp 4) * 1 := mul_le_mul_of_nonneg_left hAL2 hpos
      linarith [hstep, heq2.le, heq2.ge, hfin]
    have hlin : 2 * (2 * Lam ^ 2 * Real.exp (2 * A * Lam)) ≤ 4 * Lam ^ 2 * Real.exp 4 := by
      nlinarith [hkappa, he24, hL2]
    linarith [hsq, hlin]
  have hmin : 0 ≤ minorForm w lam s := minorForm_nonneg s hw
  have halpha : 0 ≤ alpha ^ 2 := sq_nonneg _
  calc compensatedMinor (coshWeight w lam) lam s alpha
      ≤ _ * alpha ^ 2 * minorForm w lam s := hbase
    _ ≤ 8 * Lam ^ 2 * Real.exp 4 * alpha ^ 2 * minorForm w lam s := by
        have := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hK halpha) hmin
        linarith [this]

/-! ### Assembling the `α²`-carrying budget -/

/-- The weighted variance of the log-frequencies, at the level of weights. -/
noncomputable def varForm (w lam : Fin d → ℝ) : ℝ :=
  (∑ n, w n) * (∑ n, w n * lam n ^ 2) - (∑ n, w n * lam n) ^ 2

/-- Any nonnegative weight family is the amplitude weight of a real amplitude
vector. -/
theorem ampWeight_sqrt {w : Fin d → ℝ} (hw : ∀ n, 0 ≤ w n) :
    ampWeight (fun n => ((Real.sqrt (w n) : ℝ) : ℂ)) = w := by
  funext n
  have : ‖((Real.sqrt (w n) : ℝ) : ℂ)‖ = Real.sqrt (w n) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [ampWeight, this, Real.sq_sqrt (hw n)]

/-- The weight-level log-variance ledger: `𝒜(w) ≤ s²·Var(w)`. -/
theorem minorForm_le_varForm {w lam : Fin d → ℝ} (hw : ∀ n, 0 ≤ w n) (s : ℝ) :
    minorForm w lam s ≤ s ^ 2 * varForm w lam := by
  have h := hermAnchorMinor_translate_le_logVariance
    (fun n => ((Real.sqrt (w n) : ℝ) : ℂ)) lam s
  rw [hermAnchorMinor_translate_eq_minorForm, ampWeight_sqrt hw] at h
  rw [logVariance, ampWeight_sqrt hw] at h
  exact h

/-- **The `α²`-carrying prime-side budget for the compensated observable.**
Combining the compensated bound with the log-variance ledger: for the
functional-equation weight family, with `|α| ≤ A` and log-frequencies bounded by
`Λ`,

    `𝒩(α) ≤ K·α²·s²·Var(w)`,

which is the shape `𝒫 ≤ Cδ²α²L⁶` demanded by the relative endgame once `Var(w)`
is localised.  The literal-source instantiation of `Λ`, `A` and `Var(w)` is not
performed here. -/
theorem compensatedMinor_cosh_le_varForm {w lam : Fin d → ℝ} {s alpha A Lam : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hLam : ∀ n, |lam n| ≤ Lam) (hLam0 : 0 ≤ Lam)
    (hA : |alpha| ≤ A) (hA0 : 0 ≤ A) :
    compensatedMinor (coshWeight w lam) lam s alpha
      ≤ (2 * (2 * Lam ^ 2 * Real.exp (2 * A * Lam))
          + (2 * Lam ^ 2 * Real.exp (2 * A * Lam)) ^ 2 * A ^ 2) * alpha ^ 2
        * (s ^ 2 * varForm w lam) := by
  have hbase := compensatedMinor_cosh_le (s := s) hw hLam hLam0 hA hA0
  have hled := minorForm_le_varForm (lam := lam) hw s
  have hK : 0 ≤ (2 * (2 * Lam ^ 2 * Real.exp (2 * A * Lam))
      + (2 * Lam ^ 2 * Real.exp (2 * A * Lam)) ^ 2 * A ^ 2) * alpha ^ 2 := by
    have := Real.exp_pos (2 * A * Lam); positivity
  calc compensatedMinor (coshWeight w lam) lam s alpha
      ≤ _ * minorForm w lam s := hbase
    _ ≤ _ * (s ^ 2 * varForm w lam) := mul_le_mul_of_nonneg_left hled hK

end RiemannAnalytic
