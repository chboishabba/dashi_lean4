/-
**G8.1 / Lemma 3–4 — the anchored observable expanded *before* any inequality,
and the fate of its diagonal.**

The G9 programme asks for the exact arithmetic form of the anchored observable

    `𝒜_H = ∑_{j ≠ 0} (G₀₀G_jj − |G_{0j}|²) = G₀₀ tr G − ‖G_{0,*}‖²`,

substituted entry by entry through the explicit formula, with **no triangle
inequality applied first**, and then for the verdict on its prime diagonal.

This file performs exactly that computation for the structure the explicit
formula produces: every window coordinate is a *translate* of one amplitude
family in a log-frequency variable,

    `u_s(n) = a_n · e^{i s λ_n}`   (`λ_n = log n` on the prime side),

so that the whole window is generated from one vector `a` by the unitary
translation group.  With `w_n = |a_n|²`:

* `Hsesq_translateVec` — the Hermitian Gram entry is exactly
  `∑_n w_n e^{i(s−t)λ_n}`; the diagonal entries are *all equal* to `W = ∑ w_n`,
  independently of the shift;

* `hermAnchorMinor_translate_eq` — **the exact anchored minor**:

      `Δ(s) = ∑_{n,m} w_n w_m (1 − cos(s(λ_n − λ_m)))`
            `= 2 ∑_{n,m} w_n w_m sin²(s(λ_n − λ_m)/2)`;

* `hermAnchorMinor_translate_diagonal_zero` — **the diagonal cancels
  identically.**  The terms `n = m` — which are exactly the `H ∑_n|a_n|²`
  diagonal that defeated the generic short-interval second-moment route of G7 —
  contribute *zero* to the anchored determinant.  This is the cancellation the
  determinant was supposed to provide, and it is exact, not asymptotic;

* `hermAnchorMinor_translate_le_logVariance` — what survives is a **weighted
  variance of the log-frequencies**:

      `Δ(s) ≤ s² · (W·∑_n w_nλ_n² − (∑_n w_nλ_n)²)`,

  the exact analogue, on the prime side, of the transverse-energy variance of
  `TransverseGridVariance.lean`.  The `s²` that the norm-and-count model threw
  away is present, and so is the log-frequency spread that replaces the crude
  `‖v‖²` factor;

* `logVariance_le_block` and `anchoredPrimeSum_block_budget` — the resulting
  ledger, in the only form in which it can now be improved: over a window of `q`
  shifts at spacing `h`, if the amplitude mass sits in a log-block of length `ℓ`,

      `𝒜_H ≤ ½ h² q³ W² ℓ²`.

  `anchoredPrimeBudget_critical_at_full_block` and
  `anchoredPrimeBudget_gain_of_short_block` read this at the source scale
  `h = 2π/L`, `q ≤ A₀HL`, `W ≤ C_W L`: a **full** log-block `ℓ ≍ L` returns the
  critical scale `≍ L⁶H³` (no gain — the determinant alone does not beat the
  budget), while a **short** log-block `ℓ ≤ δL` gives `≤ C·δ²·H³L⁶`.

So the verdict G9 asks for, in exact form: *the prime diagonal of the anchored
determinant cancels identically; the residual is a log-frequency variance, and
it is of critical size precisely when the amplitude mass fills the whole
log-block.*  The remaining obligation is therefore a **localisation** statement
about the prime amplitudes, not a stronger mean-value theorem — and it is not
proved here.  Nothing below assumes it.

Nothing in this file refers to `ζ`.
-/
import RiemannAnalytic.PhaseGauge

namespace RiemannAnalytic

open Finset Complex

variable {d : ℕ}

/-! ### The translated amplitude family -/

/-- The window coordinate at shift `s`: the amplitude family translated by `s`
in the log-frequency variable, `u_s(n) = a_n e^{i s λ_n}`. -/
noncomputable def translateVec (a : Fin d → ℂ) (lam : Fin d → ℝ) (s : ℝ) : Fin d → ℂ :=
  fun n => a n * Complex.exp ((s * lam n : ℝ) * Complex.I)

/-- The amplitude weights `w_n = |a_n|²`. -/
noncomputable def ampWeight (a : Fin d → ℂ) (n : Fin d) : ℝ := ‖a n‖ ^ 2

theorem ampWeight_nonneg (a : Fin d → ℂ) (n : Fin d) : 0 ≤ ampWeight a n := by
  unfold ampWeight; positivity

/-- **The Hermitian Gram entry of two translates.** -/
theorem Hsesq_translateVec (a : Fin d → ℂ) (lam : Fin d → ℝ) (s t : ℝ) :
    Hsesq (translateVec a lam s) (translateVec a lam t)
      = ∑ n, (ampWeight a n : ℂ) * Complex.exp (((s - t) * lam n : ℝ) * Complex.I) := by
  unfold Hsesq translateVec ampWeight
  refine Finset.sum_congr rfl fun n _ => ?_
  have hconj : (starRingEnd ℂ) (a n * Complex.exp ((t * lam n : ℝ) * Complex.I))
      = (starRingEnd ℂ) (a n) * Complex.exp (-((t * lam n : ℝ) * Complex.I)) := by
    rw [map_mul, ← Complex.exp_conj]
    congr 1
    simp [Complex.conj_I]
  rw [hconj]
  have hnorm : a n * (starRingEnd ℂ) (a n) = ((‖a n‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  calc a n * Complex.exp ((s * lam n : ℝ) * Complex.I) *
        ((starRingEnd ℂ) (a n) * Complex.exp (-((t * lam n : ℝ) * Complex.I)))
      = (a n * (starRingEnd ℂ) (a n)) *
          (Complex.exp ((s * lam n : ℝ) * Complex.I) *
            Complex.exp (-((t * lam n : ℝ) * Complex.I))) := by ring
    _ = ((‖a n‖ ^ 2 : ℝ) : ℂ) * Complex.exp ((((s - t) * lam n : ℝ)) * Complex.I) := by
        rw [hnorm, ← Complex.exp_add]
        congr 1
        push_cast
        ring_nf

/-- Every diagonal entry equals the total amplitude mass `W = ∑ w_n`,
independently of the shift. -/
theorem Hsesq_translateVec_self (a : Fin d → ℂ) (lam : Fin d → ℝ) (s : ℝ) :
    (Hsesq (translateVec a lam s) (translateVec a lam s)).re = ∑ n, ampWeight a n := by
  rw [Hsesq_translateVec]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp

/-! ### The exact anchored minor of two translates -/

/-- The squared modulus of a weighted exponential sum, expanded. -/
theorem normSq_weighted_exp_sum (w : Fin d → ℝ) (θ : Fin d → ℝ) :
    Complex.normSq (∑ n, (w n : ℂ) * Complex.exp ((θ n : ℝ) * Complex.I))
      = ∑ n, ∑ m, w n * w m * Real.cos (θ n - θ m) := by
  have hre : (∑ n, (w n : ℂ) * Complex.exp ((θ n : ℝ) * Complex.I)).re
      = ∑ n, w n * Real.cos (θ n) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp [Complex.exp_ofReal_mul_I_re]
  have him : (∑ n, (w n : ℂ) * Complex.exp ((θ n : ℝ) * Complex.I)).im
      = ∑ n, w n * Real.sin (θ n) := by
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp [Complex.exp_ofReal_mul_I_im]
  rw [Complex.normSq_apply, hre, him, Finset.sum_mul_sum, Finset.sum_mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Real.cos_sub]
  ring

/-- **The exact anchored minor of the translated family.**  No triangle
inequality has been used: this is an identity. -/
theorem hermAnchorMinor_translate_eq (a : Fin d → ℂ) (lam : Fin d → ℝ) (s : ℝ) :
    hermAnchorMinor (translateVec a lam 0) (translateVec a lam s)
      = ∑ n, ∑ m, ampWeight a n * ampWeight a m * (1 - Real.cos (s * (lam n - lam m))) := by
  unfold hermAnchorMinor
  rw [Hsesq_translateVec_self, Hsesq_translateVec_self, Hsesq_translateVec]
  have hns : Complex.normSq (∑ n, (ampWeight a n : ℂ) *
        Complex.exp ((((0 - s) * lam n : ℝ)) * Complex.I))
      = ∑ n, ∑ m, ampWeight a n * ampWeight a m *
          Real.cos ((0 - s) * lam n - (0 - s) * lam m) :=
    normSq_weighted_exp_sum (ampWeight a) (fun n => (0 - s) * lam n)
  rw [hns]
  have hsq : (∑ n, ampWeight a n) * (∑ n, ampWeight a n)
      = ∑ n, ∑ m, ampWeight a n * ampWeight a m := by
    rw [Finset.sum_mul_sum]
  rw [hsq, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  have harg : (0 - s) * lam n - (0 - s) * lam m = -(s * (lam n - lam m)) := by ring
  rw [harg, Real.cos_neg]
  ring

/-- **The prime diagonal cancels identically.**  Every `n = m` term of the exact
expansion is zero: the anchored determinant removes the diagonal mass
`∑_n|a_n|²` that the generic second-moment route had to pay for. -/
theorem hermAnchorMinor_translate_diagonal_zero (a : Fin d → ℂ) (lam : Fin d → ℝ)
    (s : ℝ) (n : Fin d) :
    ampWeight a n * ampWeight a n * (1 - Real.cos (s * (lam n - lam n))) = 0 := by
  simp

/-- The half-angle form: the surviving mass is an off-diagonal `sin²` sum. -/
theorem hermAnchorMinor_translate_sin (a : Fin d → ℂ) (lam : Fin d → ℝ) (s : ℝ) :
    hermAnchorMinor (translateVec a lam 0) (translateVec a lam s)
      = ∑ n, ∑ m, 2 * (ampWeight a n * ampWeight a m) *
          Real.sin (s * (lam n - lam m) / 2) ^ 2 := by
  rw [hermAnchorMinor_translate_eq]
  refine Finset.sum_congr rfl fun n _ => ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  have hsin : Real.sin (s * (lam n - lam m) / 2) ^ 2
      = (1 - Real.cos (s * (lam n - lam m))) / 2 := by
    rw [Real.sin_sq_eq_half_sub, show 2 * (s * (lam n - lam m) / 2) = s * (lam n - lam m) by ring]
    ring
  rw [hsin]
  ring

/-- Two unit phases differ by twice the cosine defect of their arguments. -/
theorem normSq_exp_diff (t p : ℝ) :
    ‖Complex.exp ((t : ℂ) * Complex.I) - Complex.exp ((p : ℂ) * Complex.I)‖ ^ 2
      = 2 * (1 - Real.cos (t - p)) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im, Real.cos_sub,
    Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  nlinarith [Real.sin_sq_add_cos_sq t, Real.sin_sq_add_cos_sq p]

/-- **The difference-kernel form predicted by G9.**  The anchored minor is a
double prime sum against the *difference* kernel `|e^{isλₙ} − e^{isλₘ}|²`.  This
is the exact statement that the determinant replaces each diagonal amplitude
mass `|aₙ|²` by a phase difference, which is the source of every gain the
norm-and-count budget threw away. -/
theorem hermAnchorMinor_translate_diffKernel (a : Fin d → ℂ) (lam : Fin d → ℝ) (s : ℝ) :
    hermAnchorMinor (translateVec a lam 0) (translateVec a lam s)
      = ∑ n, ∑ m, ampWeight a n * ampWeight a m *
          (1 / 2 * ‖Complex.exp (((s * lam n : ℝ) : ℂ) * Complex.I)
            - Complex.exp (((s * lam m : ℝ) : ℂ) * Complex.I)‖ ^ 2) := by
  rw [hermAnchorMinor_translate_eq]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
  rw [normSq_exp_diff, show s * lam n - s * lam m = s * (lam n - lam m) by ring]
  ring

/-- **A single pair bounds the anchored minor from below.**  All terms of the
exact expansion are nonnegative, so any two log-frequencies that are separated
at the scale of the shift already force the observable to be positive. -/
theorem hermAnchorMinor_translate_ge_pair (a : Fin d → ℂ) (lam : Fin d → ℝ) (s : ℝ)
    (n m : Fin d) :
    2 * (ampWeight a n * ampWeight a m) * Real.sin (s * (lam n - lam m) / 2) ^ 2
      ≤ hermAnchorMinor (translateVec a lam 0) (translateVec a lam s) := by
  rw [hermAnchorMinor_translate_sin]
  have hnn : ∀ p q : Fin d, 0 ≤ 2 * (ampWeight a p * ampWeight a q) *
      Real.sin (s * (lam p - lam q) / 2) ^ 2 := by
    intro p q
    have := mul_nonneg (ampWeight_nonneg a p) (ampWeight_nonneg a q)
    positivity
  have hrow : 2 * (ampWeight a n * ampWeight a m) * Real.sin (s * (lam n - lam m) / 2) ^ 2
      ≤ ∑ q, 2 * (ampWeight a n * ampWeight a q) *
          Real.sin (s * (lam n - lam q) / 2) ^ 2 :=
    Finset.single_le_sum (f := fun q => 2 * (ampWeight a n * ampWeight a q) *
      Real.sin (s * (lam n - lam q) / 2) ^ 2) (fun q _ => hnn n q) (Finset.mem_univ m)
  have hcol : (∑ q, 2 * (ampWeight a n * ampWeight a q) *
      Real.sin (s * (lam n - lam q) / 2) ^ 2)
      ≤ ∑ p, ∑ q, 2 * (ampWeight a p * ampWeight a q) *
          Real.sin (s * (lam p - lam q) / 2) ^ 2 :=
    Finset.single_le_sum (f := fun p => ∑ q, 2 * (ampWeight a p * ampWeight a q) *
      Real.sin (s * (lam p - lam q) / 2) ^ 2)
      (fun p _ => Finset.sum_nonneg fun q _ => hnn p q) (Finset.mem_univ n)
  linarith [hrow, hcol]

/-- **The observable really is of the size the ledger says.**  If two amplitudes
of mass at least `w₀` sit at log-frequencies whose separation is resolved by the
shift (`|sin(s(λₙ−λₘ)/2)| ≥ 1/2`), then `Δ(s) ≥ w₀²/2`: the anchored determinant
does not collapse, so the upper ledger above is not vacuous. -/
theorem hermAnchorMinor_translate_pos_of_resolved (a : Fin d → ℂ) (lam : Fin d → ℝ) (s : ℝ)
    {w0 : ℝ} (hw0 : 0 ≤ w0) (n m : Fin d)
    (hn : w0 ≤ ampWeight a n) (hm : w0 ≤ ampWeight a m)
    (hres : 1 / 2 ≤ |Real.sin (s * (lam n - lam m) / 2)|) :
    w0 ^ 2 / 2 ≤ hermAnchorMinor (translateVec a lam 0) (translateVec a lam s) := by
  have hpair := hermAnchorMinor_translate_ge_pair a lam s n m
  have hsin : (1 : ℝ) / 4 ≤ Real.sin (s * (lam n - lam m) / 2) ^ 2 := by
    have habs := sq_abs (Real.sin (s * (lam n - lam m) / 2))
    nlinarith [hres, abs_nonneg (Real.sin (s * (lam n - lam m) / 2))]
  have hw : w0 ^ 2 ≤ ampWeight a n * ampWeight a m := by nlinarith [hw0, hn, hm]
  have hstep : w0 ^ 2 / 2 ≤ 2 * (ampWeight a n * ampWeight a m) *
      Real.sin (s * (lam n - lam m) / 2) ^ 2 := by
    have hprod : 0 ≤ ampWeight a n * ampWeight a m :=
      mul_nonneg (ampWeight_nonneg a n) (ampWeight_nonneg a m)
    nlinarith [hw, hsin, hprod, sq_nonneg w0]
  linarith [hstep, hpair]

/-! ### The residual is a weighted log-frequency variance -/

/-- The weighted variance of the log-frequencies:
`Var = W·∑ w λ² − (∑ w λ)²`. -/
noncomputable def logVariance (a : Fin d → ℂ) (lam : Fin d → ℝ) : ℝ :=
  (∑ n, ampWeight a n) * (∑ n, ampWeight a n * lam n ^ 2)
    - (∑ n, ampWeight a n * lam n) ^ 2

/-- The variance in double-sum form. -/
theorem logVariance_eq_double_sum (a : Fin d → ℂ) (lam : Fin d → ℝ) :
    logVariance a lam
      = 1 / 2 * ∑ n, ∑ m, ampWeight a n * ampWeight a m * (lam n - lam m) ^ 2 := by
  set w : Fin d → ℝ := ampWeight a with hw
  set W : ℝ := ∑ n, w n with hW
  set S1 : ℝ := ∑ n, w n * lam n with hS1
  set S2 : ℝ := ∑ n, w n * lam n ^ 2 with hS2
  have hinner : ∀ n : Fin d, ∑ m, w n * w m * (lam n - lam m) ^ 2
      = (w n * lam n ^ 2) * W - (2 * (w n * lam n)) * S1 + (w n) * S2 := by
    intro n
    have hterm : ∀ m : Fin d, w n * w m * (lam n - lam m) ^ 2
        = (w n * lam n ^ 2) * w m - (2 * (w n * lam n)) * (w m * lam m)
          + (w n) * (w m * lam m ^ 2) := fun m => by ring
    rw [Finset.sum_congr rfl fun m (_ : m ∈ Finset.univ) => hterm m,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, ← hW, ← hS1, ← hS2]
  have houter : ∑ n, ∑ m, w n * w m * (lam n - lam m) ^ 2 = 2 * (W * S2 - S1 ^ 2) := by
    rw [Finset.sum_congr rfl fun n (_ : n ∈ Finset.univ) => hinner n,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      ← Finset.sum_mul]
    have e1 : ∑ n, w n * lam n ^ 2 = S2 := hS2.symm
    have e2 : ∑ n, 2 * (w n * lam n) = 2 * S1 := by
      rw [← Finset.mul_sum, ← hS1]
    have e3 : ∑ n, w n = W := hW.symm
    rw [e1, e2, e3]
    ring
  rw [houter]
  unfold logVariance
  rw [← hW, ← hS1, ← hS2]
  ring

/-- The elementary inequality `1 − cos x ≤ x²/2`, the only inequality used in
the passage from the exact expansion to the variance ledger. -/
theorem one_sub_cos_le_half_sq (x : ℝ) : 1 - Real.cos x ≤ x ^ 2 / 2 := by
  have hhalf : Real.sin (x / 2) ^ 2 = (1 - Real.cos x) / 2 := by
    rw [Real.sin_sq_eq_half_sub, show 2 * (x / 2) = x by ring]
    ring
  have hle : Real.sin (x / 2) ^ 2 ≤ (x / 2) ^ 2 := by
    have h := Real.abs_sin_le_abs (x := x / 2)
    have h1 := sq_abs (Real.sin (x / 2))
    have h2 := sq_abs (x / 2)
    nlinarith [abs_nonneg (Real.sin (x / 2)), abs_nonneg (x / 2)]
  nlinarith [hhalf, hle]

/-- **`Δ(s) ≤ s²·Var`.**  The exact expansion, bounded only by `1 − cos x ≤ x²/2`
— the one inequality that keeps both the shift factor and the log-frequency
spread. -/
theorem hermAnchorMinor_translate_le_logVariance (a : Fin d → ℂ) (lam : Fin d → ℝ) (s : ℝ) :
    hermAnchorMinor (translateVec a lam 0) (translateVec a lam s)
      ≤ s ^ 2 * logVariance a lam := by
  rw [hermAnchorMinor_translate_eq, logVariance_eq_double_sum]
  have hterm : ∀ n m : Fin d,
      ampWeight a n * ampWeight a m * (1 - Real.cos (s * (lam n - lam m)))
        ≤ ampWeight a n * ampWeight a m * ((s * (lam n - lam m)) ^ 2 / 2) := by
    intro n m
    have hcos : 1 - Real.cos (s * (lam n - lam m)) ≤ (s * (lam n - lam m)) ^ 2 / 2 :=
      one_sub_cos_le_half_sq (s * (lam n - lam m))
    have hw : 0 ≤ ampWeight a n * ampWeight a m :=
      mul_nonneg (ampWeight_nonneg a n) (ampWeight_nonneg a m)
    exact mul_le_mul_of_nonneg_left hcos hw
  calc ∑ n, ∑ m, ampWeight a n * ampWeight a m * (1 - Real.cos (s * (lam n - lam m)))
      ≤ ∑ n, ∑ m, ampWeight a n * ampWeight a m * ((s * (lam n - lam m)) ^ 2 / 2) :=
        Finset.sum_le_sum fun n _ => Finset.sum_le_sum fun m _ => hterm n m
    _ = s ^ 2 * (1 / 2 * ∑ n, ∑ m, ampWeight a n * ampWeight a m * (lam n - lam m) ^ 2) := by
        have hstep : ∀ n : Fin d,
            ∑ m, ampWeight a n * ampWeight a m * ((s * (lam n - lam m)) ^ 2 / 2)
              = (s ^ 2 / 2) * ∑ m, ampWeight a n * ampWeight a m * (lam n - lam m) ^ 2 := by
          intro n
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun m _ => by ring
        rw [Finset.sum_congr rfl fun n (_ : n ∈ Finset.univ) => hstep n, ← Finset.mul_sum]
        ring

/-- **The variance is controlled by the log-block length.**  If all
log-frequencies lie in an interval of length `ℓ`, then `Var ≤ W²ℓ²`. -/
theorem logVariance_le_block (a : Fin d → ℂ) (lam : Fin d → ℝ) {c l : ℝ} (hl : 0 ≤ l)
    (hblock : ∀ n, lam n ∈ Set.Icc c (c + l)) :
    logVariance a lam ≤ (∑ n, ampWeight a n) ^ 2 * l ^ 2 := by
  set w : Fin d → ℝ := ampWeight a with hw
  set W : ℝ := ∑ n, w n with hW
  have hwnn : ∀ n, 0 ≤ w n := fun n => ampWeight_nonneg a n
  have hWnn : 0 ≤ W := Finset.sum_nonneg fun n _ => hwnn n
  have hterm : ∀ n m : Fin d, w n * w m * (lam n - lam m) ^ 2 ≤ (w n * l ^ 2) * w m := by
    intro n m
    have hn := hblock n
    have hm := hblock m
    have habs : |lam n - lam m| ≤ l := by
      rw [abs_le]
      constructor <;> [linarith [hn.1, hm.2]; linarith [hn.2, hm.1]]
    have hsq : (lam n - lam m) ^ 2 ≤ l ^ 2 := by
      have h1 := sq_abs (lam n - lam m)
      nlinarith [abs_nonneg (lam n - lam m)]
    have hprod : 0 ≤ w n * w m := mul_nonneg (hwnn n) (hwnn m)
    nlinarith [hprod, hsq]
  have hinner : ∀ n : Fin d, ∑ m, w n * w m * (lam n - lam m) ^ 2 ≤ (w n * l ^ 2) * W := by
    intro n
    calc ∑ m, w n * w m * (lam n - lam m) ^ 2
        ≤ ∑ m, (w n * l ^ 2) * w m := Finset.sum_le_sum fun m _ => hterm n m
      _ = (w n * l ^ 2) * W := by rw [← Finset.mul_sum, ← hW]
  have hsum : ∑ n, ∑ m, w n * w m * (lam n - lam m) ^ 2 ≤ W ^ 2 * l ^ 2 := by
    calc ∑ n, ∑ m, w n * w m * (lam n - lam m) ^ 2
        ≤ ∑ n, (w n * l ^ 2) * W := Finset.sum_le_sum fun n _ => hinner n
      _ = W ^ 2 * l ^ 2 := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← hW]
          ring
  have hnn : 0 ≤ W ^ 2 * l ^ 2 := by positivity
  rw [logVariance_eq_double_sum]
  linarith [hsum, hnn]

/-! ### The window ledger in prime coordinates -/

/-- **The anchored observable of a shift window, in prime coordinates.**  Over a
grid of `q` shifts at spacing `h`, with amplitude mass `W` in a log-block of
length `ℓ`, the anchored observable is at most `h²q³W²ℓ²`. -/
theorem anchoredPrimeSum_block_budget (a : Fin d → ℂ) (lam : Fin d → ℝ) {c l h : ℝ}
    {q : ℕ} (hl : 0 ≤ l) (hblock : ∀ n, lam n ∈ Set.Icc c (c + l)) :
    ∑ j : Fin q, hermAnchorMinor (translateVec a lam 0)
        (translateVec a lam (h * ((j : ℕ) : ℝ)))
      ≤ h ^ 2 * (q : ℝ) ^ 3 * ((∑ n, ampWeight a n) ^ 2 * l ^ 2) := by
  have hV : logVariance a lam ≤ (∑ n, ampWeight a n) ^ 2 * l ^ 2 :=
    logVariance_le_block a lam hl hblock
  have hVnn : 0 ≤ (∑ n, ampWeight a n) ^ 2 * l ^ 2 := by positivity
  have hterm : ∀ j : Fin q, hermAnchorMinor (translateVec a lam 0)
      (translateVec a lam (h * ((j : ℕ) : ℝ)))
        ≤ (h * ((j : ℕ) : ℝ)) ^ 2 * ((∑ n, ampWeight a n) ^ 2 * l ^ 2) := by
    intro j
    refine (hermAnchorMinor_translate_le_logVariance a lam _).trans ?_
    exact mul_le_mul_of_nonneg_left hV (by positivity)
  refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
  have hcount : ∑ j : Fin q, (h * ((j : ℕ) : ℝ)) ^ 2 ≤ h ^ 2 * (q : ℝ) ^ 3 := by
    have hterm2 : ∀ j : Fin q, (h * ((j : ℕ) : ℝ)) ^ 2 ≤ h ^ 2 * (q : ℝ) ^ 2 := by
      intro j
      have hj : ((j : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast j.isLt.le
      have hj0 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
      have hjsq : ((j : ℕ) : ℝ) ^ 2 ≤ (q : ℝ) ^ 2 := by nlinarith
      calc (h * ((j : ℕ) : ℝ)) ^ 2 = h ^ 2 * ((j : ℕ) : ℝ) ^ 2 := by ring
        _ ≤ h ^ 2 * (q : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hjsq (by positivity)
    calc ∑ j : Fin q, (h * ((j : ℕ) : ℝ)) ^ 2
        ≤ ∑ _j : Fin q, h ^ 2 * (q : ℝ) ^ 2 := Finset.sum_le_sum fun j _ => hterm2 j
      _ = (q : ℝ) * (h ^ 2 * (q : ℝ) ^ 2) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = h ^ 2 * (q : ℝ) ^ 3 := by ring
  calc ∑ j : Fin q, (h * ((j : ℕ) : ℝ)) ^ 2 * ((∑ n, ampWeight a n) ^ 2 * l ^ 2)
      = (∑ j : Fin q, (h * ((j : ℕ) : ℝ)) ^ 2) * ((∑ n, ampWeight a n) ^ 2 * l ^ 2) := by
        rw [Finset.sum_mul]
    _ ≤ (h ^ 2 * (q : ℝ) ^ 3) * ((∑ n, ampWeight a n) ^ 2 * l ^ 2) :=
        mul_le_mul_of_nonneg_right hcount hVnn
    _ = h ^ 2 * (q : ℝ) ^ 3 * ((∑ n, ampWeight a n) ^ 2 * l ^ 2) := by ring

/-! ### Reading the ledger at the source scale -/

/-- The source-scaled prime budget: spacing `2π/L`, window count `A₀HL`,
amplitude mass `C_W L`, log-block length `ℓ`. -/
noncomputable def primeBlockBudget (A0 CW : ℝ) (L H l : ℝ) : ℝ :=
  4 * Real.pi ^ 2 * A0 ^ 3 * CW ^ 2 * L ^ 3 * H ^ 3 * l ^ 2

theorem anchoredPrimeSum_source_budget (a : Fin d → ℂ) (lam : Fin d → ℝ)
    {c l A0 CW L H : ℝ} {q : ℕ} (hL : 0 < L) (hl : 0 ≤ l)
    (hblock : ∀ n, lam n ∈ Set.Icc c (c + l))
    (hq : (q : ℝ) ≤ A0 * H * L) (hW : ∑ n, ampWeight a n ≤ CW * L) (hCW : 0 ≤ CW)
    (hA0 : 0 ≤ A0) (hH : 0 ≤ H) :
    ∑ j : Fin q, hermAnchorMinor (translateVec a lam 0)
        (translateVec a lam (2 * Real.pi / L * ((j : ℕ) : ℝ)))
      ≤ primeBlockBudget A0 CW L H l := by
  have hbase := anchoredPrimeSum_block_budget (q := q) a lam (h := 2 * Real.pi / L) hl hblock
  refine hbase.trans ?_
  have hWnn : 0 ≤ ∑ n, ampWeight a n :=
    Finset.sum_nonneg fun n _ => ampWeight_nonneg a n
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg _
  have hcube : (q : ℝ) ^ 3 ≤ (A0 * H * L) ^ 3 := pow_le_pow_left₀ hq0 hq 3
  have hWsq : (∑ n, ampWeight a n) ^ 2 ≤ (CW * L) ^ 2 := by
    have : 0 ≤ CW * L := by positivity
    nlinarith [hWnn, hW]
  have h1 : (2 * Real.pi / L) ^ 2 * (q : ℝ) ^ 3 * ((∑ n, ampWeight a n) ^ 2 * l ^ 2)
      ≤ (2 * Real.pi / L) ^ 2 * (A0 * H * L) ^ 3 * ((CW * L) ^ 2 * l ^ 2) := by
    have hstep1 : (q : ℝ) ^ 3 * ((∑ n, ampWeight a n) ^ 2 * l ^ 2)
        ≤ (A0 * H * L) ^ 3 * ((CW * L) ^ 2 * l ^ 2) := by
      have hA : 0 ≤ (A0 * H * L) ^ 3 := by positivity
      have hWl : (∑ n, ampWeight a n) ^ 2 * l ^ 2 ≤ (CW * L) ^ 2 * l ^ 2 :=
        mul_le_mul_of_nonneg_right hWsq (sq_nonneg l)
      calc (q : ℝ) ^ 3 * ((∑ n, ampWeight a n) ^ 2 * l ^ 2)
          ≤ (A0 * H * L) ^ 3 * ((∑ n, ampWeight a n) ^ 2 * l ^ 2) :=
            mul_le_mul_of_nonneg_right hcube (by positivity)
        _ ≤ (A0 * H * L) ^ 3 * ((CW * L) ^ 2 * l ^ 2) :=
            mul_le_mul_of_nonneg_left hWl hA
    have hpre : (0 : ℝ) ≤ (2 * Real.pi / L) ^ 2 := by positivity
    calc (2 * Real.pi / L) ^ 2 * (q : ℝ) ^ 3 * ((∑ n, ampWeight a n) ^ 2 * l ^ 2)
        = (2 * Real.pi / L) ^ 2 * ((q : ℝ) ^ 3 * ((∑ n, ampWeight a n) ^ 2 * l ^ 2)) := by
          ring
      _ ≤ (2 * Real.pi / L) ^ 2 * ((A0 * H * L) ^ 3 * ((CW * L) ^ 2 * l ^ 2)) :=
          mul_le_mul_of_nonneg_left hstep1 hpre
      _ = (2 * Real.pi / L) ^ 2 * (A0 * H * L) ^ 3 * ((CW * L) ^ 2 * l ^ 2) := by ring
  refine h1.trans (le_of_eq ?_)
  unfold primeBlockBudget
  have hLne : L ≠ 0 := ne_of_gt hL
  field_simp
  ring

/-- **A full log-block returns the critical scale.**  With `ℓ = L` the
source-scaled prime budget is exactly a constant times `L⁵H³`, hence at most the
critical `L⁶H³` and no better: the determinant alone does not beat the budget
when the amplitude mass fills the whole log-block. -/
theorem anchoredPrimeBudget_full_block (A0 CW L H : ℝ) :
    primeBlockBudget A0 CW L H L = 4 * Real.pi ^ 2 * A0 ^ 3 * CW ^ 2 * L ^ 5 * H ^ 3 := by
  unfold primeBlockBudget
  ring

/-- **A short log-block gains.**  If the amplitude mass sits in a log-block of
length `ℓ ≤ δL`, the budget improves by the factor `δ²`. -/
theorem anchoredPrimeBudget_gain_of_short_block {A0 CW L H delta l : ℝ}
    (hA0 : 0 ≤ A0) (hL : 0 ≤ L) (hH : 0 ≤ H) (hl : 0 ≤ l) (hshort : l ≤ delta * L) :
    primeBlockBudget A0 CW L H l
      ≤ 4 * Real.pi ^ 2 * A0 ^ 3 * CW ^ 2 * delta ^ 2 * L ^ 5 * H ^ 3 := by
  unfold primeBlockBudget
  have hlsq : l ^ 2 ≤ (delta * L) ^ 2 := by nlinarith [hl, hshort]
  have hC : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * A0 ^ 3 * CW ^ 2 * L ^ 3 * H ^ 3 := by
    have := Real.pi_pos; positivity
  nlinarith [mul_le_mul_of_nonneg_left hlsq hC]

/-! ## The raw anchored prime observable cannot carry the factor `α²`

The relative endgame (`RiemannAnalytic.RelativeContraction`) needs a prime bound
of the form `𝒫 ≤ Cδ²α²L⁶`, i.e. one that *vanishes on the critical line*.  The
next theorem is a hard obstruction: as soon as the amplitude family has a
resolved pair of log-frequencies at the baseline `α = 0` — which is the generic
situation, and exactly the hypothesis under which the G9 ledger is non-vacuous —
the raw anchored prime observable is bounded below by a positive constant at
`α = 0`, so **no** bound proportional to `α²` can hold for it.

The consequence is structural, and matches the gauge analysis of `PhaseGauge`:
the `α²`-carrying quantity must be a *baseline-subtracted* (compensated)
observable `𝒟(α) = 𝒦(α) − 𝒦(0)`, never the raw anchored prime sum. -/

/-- **No `α²` factor for the raw observable.**  If at the baseline the amplitude
family has two log-frequencies resolved by the shift, the anchored minor of the
family is positive at `α = 0`, so it admits no bound of the form `Cα²L⁶`. -/
theorem anchoredPrime_no_alpha_factor_of_positive_baseline
    (aFam : ℝ → (Fin d → ℂ)) (lam : Fin d → ℝ) (s : ℝ) {w0 : ℝ} (hw0 : 0 < w0)
    (n m : Fin d)
    (hn : w0 ≤ ampWeight (aFam 0) n) (hm : w0 ≤ ampWeight (aFam 0) m)
    (hres : 1 / 2 ≤ |Real.sin (s * (lam n - lam m) / 2)|) :
    ¬ ∃ C L : ℝ, ∀ alpha : ℝ,
      hermAnchorMinor (translateVec (aFam alpha) lam 0) (translateVec (aFam alpha) lam s)
        ≤ C * alpha ^ 2 * L ^ 6 := by
  rintro ⟨C, L, hbound⟩
  have hbase := hermAnchorMinor_translate_pos_of_resolved (aFam 0) lam s
    (le_of_lt hw0) n m hn hm hres
  have h0 := hbound 0
  simp at h0
  nlinarith [hbase, h0]

end RiemannAnalytic
