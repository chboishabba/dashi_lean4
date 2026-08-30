import RiemannAnalytic.TwistedPrimeVarianceLower
import RiemannAnalytic.TwistedPrimeMassMean
import RiemannAnalytic.TwistedNormalization
import RiemannAnalytic.CompensatedDiagonal
import RiemannAnalytic.RelativeContraction

/-!
# G14 — the literal anchored prime observable at exact scale, and the source
normalization decision

G13 computed the twisted prime moments and proved that the *relative* log
variance of the literal cosh-twisted von Mangoldt measure is `Θ(1)`:

```
10⁻⁷ S₀²  ≤  S₀S₂ − S₁²  ≤  15000 S₀².
```

This module turns that into a statement about the object the programme actually
consumes — the anchored observable

```
𝒜_N(α, t) = ∑_{n,m ≤ N} w_α(n) w_α(m) (1 − cos(t(log n − log m))),
     w_α(n) = Λ(n) cosh(2α log n),
```

and about its compensated (baseline-subtracted) version
`𝒟_N(α,t) = 𝒜_N(α,t) − 𝒜_N(0,t)`.

Main results.

* `pairForm_le_logVar`, `pairForm_ge_logVar_of_small_phase` — the anchored
  observable of *any* nonnegative weight family is pinned between `½t²V` and
  `t²V`, where `V` is the weighted log-variance `S₀S₂ − S₁²`; the lower bound
  needs only that every pair phase satisfies `|t Δλ| ≤ 1`.
* `zetaAnchoredPrimeForm_two_sided` — the literal instantiation:
  `t²S₀²/(2·10⁷) ≤ 𝒜_N(α,t) ≤ 15000 t² S₀²`, uniformly for `|α| < 1/2`.
  **So the literal prime side of the route is exactly of size `t²S₀²`, up to
  absolute constants, and no rearrangement of the prime sum can change that.**
* `zetaCompensatedPrimeForm_le_twisted` — the compensated observable carries the
  factor `α²` against the *twisted* mass, with a polynomial constant:
  `𝒟_N(α,t) ≤ 8(log N)²α²·𝒜_N(α,t)`; hence
  `zetaCompensatedPrimeForm_le`:
  `𝒟_N(α,t) ≤ 120000 (log N)² α² t² S₀²`.
* `offLineZero_excluded_of_sourceNormalization` and its `sourceRatio` form — the
  **decision theorem**.  Given the (still unproved) source identification
  `D_{ρ,H} ≤ C_src · 𝒟_N(α,t)` and the geometric floor `cL⁶α² ≤ D_{ρ,H}`, the
  off-line displacement is exactly zero as soon as

```
120000 (log N)² · C_src t² S₀² < c L⁶,     i.e.    120000 (log N)² Q < c,
Q = C_src t² S₀² / L⁶.
```

  The `α²` cancels between the compensated prime bound and the floor, exactly as
  the relative architecture predicts: the surviving condition does not involve
  `α` at all.  It is a pure comparison between the source normalization constant
  and the Gram floor constant.

* `zetaCompensatedPrimeForm_ge` — the **matching lower bound**
  `10⁻¹⁴ α² t² ψ(N)² ≤ 𝒟_N(α,t)` (small-phase regime), proved from the exact
  quadratic lower bound for the twist, the diagonal Taylor kernel bound and
  Cauchy–Schwarz against the G13 log-variance lower bound.  So the compensated
  prime observable is pinned to `α²t²S₀²` from both sides, and
  `primeBudget_not_contractive` records the negative half of the decision: if
  the source normalization is large, the prime term alone is at least the whole
  defect and no contraction is available.
* `sourceNormalization_forced_scale` — substituting the computed prime side into
  the contraction condition in the route's own normalization `L = log N` forces

```
C_src · t² · N < 3c,
```

  and `contraction_condition_fails_of_fixed_normalization` turns this into an
  explicit threshold: **no fixed (or slowly decaying) source normalization can
  close the route**; the source must supply a factor of order `1/N ≍ 1/S₀`.

Nothing here proves the source identification `D_{ρ,H} ≤ C_src·𝒟_N(α,t)`; that
is an explicit hypothesis of the consumer theorems, and it remains this
programme's first unproved theorem.  Nothing here proves the Riemann
Hypothesis.
-/

open Finset Real ArithmeticFunction

namespace RiemannAnalytic

/-! ### The anchored pair form of a general nonnegative weight family -/

/-- The anchored observable of a weight family `w` with log-frequencies `l`
on a finite index set: `∑_{n,m} w_n w_m (1 − cos(t(l_n − l_m)))`. -/
noncomputable def pairForm (s : Finset ℕ) (w l : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ n ∈ s, ∑ m ∈ s, w n * w m * (1 - Real.cos (t * (l n - l m)))

/-- The weighted log-variance `S₀S₂ − S₁²` of a weight family. -/
noncomputable def logVar (s : Finset ℕ) (w l : ℕ → ℝ) : ℝ :=
  (∑ n ∈ s, w n) * (∑ n ∈ s, w n * (l n) ^ 2) - (∑ n ∈ s, w n * l n) ^ 2

theorem pairForm_nonneg {s : Finset ℕ} {w l : ℕ → ℝ} (hw : ∀ n ∈ s, 0 ≤ w n) (t : ℝ) :
    0 ≤ pairForm s w l t := by
  refine Finset.sum_nonneg fun n hn => Finset.sum_nonneg fun m hm => ?_
  have hcos : 0 ≤ 1 - Real.cos (t * (l n - l m)) := by
    have := Real.cos_le_one (t * (l n - l m)); linarith
  exact mul_nonneg (mul_nonneg (hw n hn) (hw m hm)) hcos

/-- **The anchored observable never exceeds `t²` times the log-variance.**  This
is the diagonal-cancellation (Taylor) gain in its exact global form. -/
theorem pairForm_le_logVar {s : Finset ℕ} {w l : ℕ → ℝ} (hw : ∀ n ∈ s, 0 ≤ w n) (t : ℝ) :
    pairForm s w l t ≤ t ^ 2 * logVar s w l := by
  have hstep : pairForm s w l t
      ≤ ∑ n ∈ s, ∑ m ∈ s, t ^ 2 / 2 * (w n * w m * (l n - l m) ^ 2) := by
    refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => ?_
    have hk : 1 - Real.cos (t * (l n - l m)) ≤ (t * (l n - l m)) ^ 2 / 2 :=
      one_sub_cos_le_half_sq _
    have hww : 0 ≤ w n * w m := mul_nonneg (hw n hn) (hw m hm)
    nlinarith [mul_le_mul_of_nonneg_left hk hww]
  have hsum : ∑ n ∈ s, ∑ m ∈ s, t ^ 2 / 2 * (w n * w m * (l n - l m) ^ 2)
      = t ^ 2 / 2 * ∑ n ∈ s, ∑ m ∈ s, w n * w m * (l n - l m) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [Finset.mul_sum]
  rw [hsum] at hstep
  have hid := varForm_eq_double s w l
  unfold logVar
  rw [hid]
  linarith [hstep]

/-- **The matching lower bound.**  As soon as every pair phase satisfies
`|t(l_n − l_m)| ≤ 1`, the anchored observable is at least `½t²` times the
log-variance.  Together with `pairForm_le_logVar` the observable is pinned to
`t²·(log-variance)` within a factor `2`. -/
theorem pairForm_ge_logVar_of_small_phase {s : Finset ℕ} {w l : ℕ → ℝ}
    (hw : ∀ n ∈ s, 0 ≤ w n) {t : ℝ}
    (hphase : ∀ n ∈ s, ∀ m ∈ s, |t * (l n - l m)| ≤ 1) :
    t ^ 2 / 2 * logVar s w l ≤ pairForm s w l t := by
  have hstep : ∑ n ∈ s, ∑ m ∈ s, t ^ 2 / 4 * (w n * w m * (l n - l m) ^ 2)
      ≤ pairForm s w l t := by
    refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => ?_
    have hk : (t * (l n - l m)) ^ 2 / 4 ≤ 1 - Real.cos (t * (l n - l m)) :=
      quarter_sq_le_one_sub_cos (hphase n hn m hm)
    have hww : 0 ≤ w n * w m := mul_nonneg (hw n hn) (hw m hm)
    nlinarith [mul_le_mul_of_nonneg_left hk hww]
  have hsum : ∑ n ∈ s, ∑ m ∈ s, t ^ 2 / 4 * (w n * w m * (l n - l m) ^ 2)
      = t ^ 2 / 4 * ∑ n ∈ s, ∑ m ∈ s, w n * w m * (l n - l m) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [Finset.mul_sum]
  rw [hsum] at hstep
  have hid := varForm_eq_double s w l
  unfold logVar
  rw [hid]
  linarith [hstep]

/-! ### The literal zeta instantiation -/

/-- The literal anchored prime observable: the anchored pair form of the
cosh-twisted von Mangoldt weights on `[1, N]` with log-frequencies `log n`. -/
noncomputable def zetaAnchoredPrimeForm (N : ℕ) (α t : ℝ) : ℝ :=
  pairForm (Icc 1 N) (coshVonMangoldt α) (fun n => Real.log n) t

/-- The literal compensated (baseline-subtracted) prime observable
`𝒟_N(α,t) = 𝒜_N(α,t) − 𝒜_N(0,t)`. -/
noncomputable def zetaCompensatedPrimeForm (N : ℕ) (α t : ℝ) : ℝ :=
  zetaAnchoredPrimeForm N α t - zetaAnchoredPrimeForm N 0 t

theorem coshVonMangoldt_zero_twist (n : ℕ) : coshVonMangoldt 0 n = Λ n := by
  simp [coshVonMangoldt]

theorem logVar_icc_eq (N : ℕ) (α : ℝ) :
    logVar (Icc 1 N) (coshVonMangoldt α) (fun n => Real.log n)
      = twistedMoment N α 0 * twistedMoment N α 2 - (twistedMoment N α 1) ^ 2 := by
  simp [logVar, twistedMoment]

theorem zetaAnchoredPrimeForm_nonneg (N : ℕ) (α t : ℝ) :
    0 ≤ zetaAnchoredPrimeForm N α t :=
  pairForm_nonneg (fun n _ => coshVonMangoldt_nonneg α n) t

/-- **The literal upper bound.**  `𝒜_N(α,t) ≤ 15000 t² S₀²`, uniformly for every
off-line displacement `|α| < 1/2`. -/
theorem zetaAnchoredPrimeForm_le {N : ℕ} (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ))
    {α : ℝ} (hα : |α| < 1 / 2) (t : ℝ) :
    zetaAnchoredPrimeForm N α t ≤ 15000 * t ^ 2 * (twistedMoment N α 0) ^ 2 := by
  have h1 := pairForm_le_logVar (s := Icc 1 N) (w := coshVonMangoldt α)
    (l := fun n => Real.log n) (fun n _ => coshVonMangoldt_nonneg α n) t
  rw [logVar_icc_eq] at h1
  have h2 := zetaTwistedPrimeCenteredVariance hN hα
  have ht : (0 : ℝ) ≤ t ^ 2 := sq_nonneg t
  have := mul_le_mul_of_nonneg_left h2 ht
  unfold zetaAnchoredPrimeForm
  nlinarith [h1, this]

/-- Every log-frequency of the index set `[1,N]` lies in `[0, log N]`, so every
pair phase is at most `|t| log N`. -/
theorem zeta_phase_le {N : ℕ} {t : ℝ} (ht : |t| * Real.log N ≤ 1) :
    ∀ n ∈ Icc 1 N, ∀ m ∈ Icc 1 N, |t * (Real.log n - Real.log m)| ≤ 1 := by
  intro n hn m hm
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
  obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
  have hlogn0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlogm0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hlognN : Real.log n ≤ Real.log N := by
    apply Real.log_le_log (by exact_mod_cast hn1)
    exact_mod_cast hnN
  have hlogmN : Real.log m ≤ Real.log N := by
    apply Real.log_le_log (by exact_mod_cast hm1)
    exact_mod_cast hmN
  have hdiff : |Real.log n - Real.log m| ≤ Real.log N := by
    rw [abs_le]; constructor <;> linarith
  calc |t * (Real.log n - Real.log m)| = |t| * |Real.log n - Real.log m| := abs_mul _ _
    _ ≤ |t| * Real.log N := mul_le_mul_of_nonneg_left hdiff (abs_nonneg t)
    _ ≤ 1 := ht

/-- **The literal lower bound.**  In the small-phase regime `|t| log N ≤ 1` the
anchored prime observable is at least `t²S₀²/(2·10⁷)`, uniformly in `|α| < 1/2`.
This is the theorem that removes the last hope of a *prime-side* gain: the
observable is not merely bounded above by `t²S₀²`, it is bounded below by an
absolute multiple of the same quantity. -/
theorem zetaAnchoredPrimeForm_ge {N : ℕ} (hN : (10 : ℝ) ^ 9 ≤ (N : ℝ))
    {α : ℝ} (hα : |α| < 1 / 2) {t : ℝ} (ht : |t| * Real.log N ≤ 1) :
    t ^ 2 / (2 * 10 ^ 7) * (twistedMoment N α 0) ^ 2 ≤ zetaAnchoredPrimeForm N α t := by
  have h1 := pairForm_ge_logVar_of_small_phase (s := Icc 1 N) (w := coshVonMangoldt α)
    (l := fun n => Real.log n) (fun n _ => coshVonMangoldt_nonneg α n) (zeta_phase_le ht)
  rw [logVar_icc_eq] at h1
  have h2 := zetaTwistedPrimeVariance_lower hN hα
  have ht2 : (0 : ℝ) ≤ t ^ 2 / 2 := by positivity
  have := mul_le_mul_of_nonneg_left h2 ht2
  unfold zetaAnchoredPrimeForm
  nlinarith [h1, this]

/-- **The literal anchored prime observable, two-sided.**  Its size is exactly
`t²S₀²` up to absolute constants, uniformly in the off-line displacement.  The
prime side therefore carries **no** hidden small factor; the whole route depends
on the source normalization in front of it. -/
theorem zetaAnchoredPrimeForm_two_sided {N : ℕ} (hN : (10 : ℝ) ^ 9 ≤ (N : ℝ))
    {α : ℝ} (hα : |α| < 1 / 2) {t : ℝ} (ht : |t| * Real.log N ≤ 1) :
    t ^ 2 / (2 * 10 ^ 7) * (twistedMoment N α 0) ^ 2 ≤ zetaAnchoredPrimeForm N α t ∧
      zetaAnchoredPrimeForm N α t ≤ 15000 * t ^ 2 * (twistedMoment N α 0) ^ 2 := by
  have hN8 : (10 : ℝ) ^ 8 ≤ (N : ℝ) := le_trans (by norm_num) hN
  exact ⟨zetaAnchoredPrimeForm_ge hN hα ht, zetaAnchoredPrimeForm_le hN8 hα t⟩

/-! ### The compensated observable carries `α²` -/

/-- **The compensated prime observable against the twisted mass.**  The literal
baseline subtraction gains a factor `8(log N)²α²` — polynomial in the
log-frequency range, uniform in `α`, and with no exponential factor, because the
comparison is made against the *twisted* observable. -/
theorem zetaCompensatedPrimeForm_le_twisted (N : ℕ) (α t : ℝ) :
    zetaCompensatedPrimeForm N α t
      ≤ 8 * (Real.log N) ^ 2 * α ^ 2 * zetaAnchoredPrimeForm N α t := by
  have hkey : ∀ n ∈ Icc 1 N, ∀ m ∈ Icc 1 N,
      coshVonMangoldt α n * coshVonMangoldt α m *
          (1 - Real.cos (t * (Real.log n - Real.log m)))
        - coshVonMangoldt 0 n * coshVonMangoldt 0 m *
          (1 - Real.cos (t * (Real.log n - Real.log m)))
        ≤ 8 * (Real.log N) ^ 2 * α ^ 2 *
          (coshVonMangoldt α n * coshVonMangoldt α m *
            (1 - Real.cos (t * (Real.log n - Real.log m)))) := by
    intro n hn m hm
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hlogn0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    have hlogm0 : 0 ≤ Real.log m := Real.log_natCast_nonneg m
    have hlognN : Real.log n ≤ Real.log N := by
      apply Real.log_le_log (by exact_mod_cast hn1); exact_mod_cast hnN
    have hlogmN : Real.log m ≤ Real.log N := by
      apply Real.log_le_log (by exact_mod_cast hm1); exact_mod_cast hmN
    have hsqn : (Real.log n) ^ 2 ≤ (Real.log N) ^ 2 := by nlinarith
    have hsqm : (Real.log m) ^ 2 ≤ (Real.log N) ^ 2 := by nlinarith
    have hLn : 0 ≤ Λ n := vonMangoldt_nonneg
    have hLm : 0 ≤ Λ m := vonMangoldt_nonneg
    have hcos : 0 ≤ 1 - Real.cos (t * (Real.log n - Real.log m)) := by
      have := Real.cos_le_one (t * (Real.log n - Real.log m)); linarith
    have hpair := coshProd_sub_one_le_twisted (2 * α * Real.log n) (2 * α * Real.log m)
    have hcn : 0 < Real.cosh (2 * α * Real.log n) := Real.cosh_pos _
    have hcm : 0 < Real.cosh (2 * α * Real.log m) := Real.cosh_pos _
    have hsq : (2 * α * Real.log n) ^ 2 + (2 * α * Real.log m) ^ 2
        ≤ 8 * (Real.log N) ^ 2 * α ^ 2 := by nlinarith [sq_nonneg α]
    have hprod : Real.cosh (2 * α * Real.log n) * Real.cosh (2 * α * Real.log m) - 1
        ≤ 8 * (Real.log N) ^ 2 * α ^ 2 *
          (Real.cosh (2 * α * Real.log n) * Real.cosh (2 * α * Real.log m)) := by
      have hcc : 0 < Real.cosh (2 * α * Real.log n) * Real.cosh (2 * α * Real.log m) :=
        mul_pos hcn hcm
      nlinarith [hpair, hsq, hcc]
    have hmul : Λ n * Λ m * (1 - Real.cos (t * (Real.log n - Real.log m))) *
        (Real.cosh (2 * α * Real.log n) * Real.cosh (2 * α * Real.log m) - 1)
        ≤ Λ n * Λ m * (1 - Real.cos (t * (Real.log n - Real.log m))) *
          (8 * (Real.log N) ^ 2 * α ^ 2 *
            (Real.cosh (2 * α * Real.log n) * Real.cosh (2 * α * Real.log m))) := by
      have hfac : 0 ≤ Λ n * Λ m * (1 - Real.cos (t * (Real.log n - Real.log m))) :=
        mul_nonneg (mul_nonneg hLn hLm) hcos
      exact mul_le_mul_of_nonneg_left hprod hfac
    simp only [coshVonMangoldt, mul_zero, zero_mul, Real.cosh_zero, mul_one]
    nlinarith [hmul]
  have hsplit : zetaCompensatedPrimeForm N α t
      = ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N,
          (coshVonMangoldt α n * coshVonMangoldt α m *
              (1 - Real.cos (t * (Real.log n - Real.log m)))
            - coshVonMangoldt 0 n * coshVonMangoldt 0 m *
              (1 - Real.cos (t * (Real.log n - Real.log m)))) := by
    unfold zetaCompensatedPrimeForm zetaAnchoredPrimeForm pairForm
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by rw [← Finset.sum_sub_distrib]
  have hrhs : 8 * (Real.log N) ^ 2 * α ^ 2 * zetaAnchoredPrimeForm N α t
      = ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N,
          8 * (Real.log N) ^ 2 * α ^ 2 *
            (coshVonMangoldt α n * coshVonMangoldt α m *
              (1 - Real.cos (t * (Real.log n - Real.log m)))) := by
    unfold zetaAnchoredPrimeForm pairForm
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [Finset.mul_sum]
  rw [hsplit, hrhs]
  exact Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => hkey n hn m hm

/-- **The literal compensated prime bound.**  Combining the `α²` gain of the
baseline subtraction with the computed scale of the anchored observable:

```
𝒟_N(α,t)  ≤  120000 (log N)² α² t² S₀².
```

Every factor here is explicit and every one is proved. -/
theorem zetaCompensatedPrimeForm_le {N : ℕ} (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ))
    {α : ℝ} (hα : |α| < 1 / 2) (t : ℝ) :
    zetaCompensatedPrimeForm N α t
      ≤ 120000 * (Real.log N) ^ 2 * α ^ 2 * t ^ 2 * (twistedMoment N α 0) ^ 2 := by
  have h1 := zetaCompensatedPrimeForm_le_twisted N α t
  have h2 := zetaAnchoredPrimeForm_le hN hα t
  have hfac : (0 : ℝ) ≤ 8 * (Real.log N) ^ 2 * α ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left h2 hfac
  nlinarith [h1, this]

/-! ### The decision theorem -/

/-- The **source normalization ratio** `Q = C_src t² S₀² / L⁶`: the single
quantity on which the anchored second-moment route now turns. -/
noncomputable def sourceRatio (N : ℕ) (α t Csrc L : ℝ) : ℝ :=
  Csrc * t ^ 2 * (twistedMoment N α 0) ^ 2 / L ^ 6

/-- **The source-normalization decision theorem.**  Suppose

* the literal anchored defect of an off-line target is dominated by the source
  constant times the compensated prime observable, `D ≤ C_src·𝒟_N(α,t)`
  (this is the still-unproved identification, supplied here as a hypothesis);
* the geometric Gram floor `cL⁶α² ≤ D` holds;
* the source normalization satisfies `120000 (log N)² C_src t² S₀² < cL⁶`.

Then the off-line displacement is **exactly** zero.

Note what has disappeared: the displacement `α` does not occur in the third
hypothesis.  The `α²` of the compensated prime bound cancels against the `α²` of
the geometric floor, so the whole route reduces to a comparison of two
constants. -/
theorem offLineZero_excluded_of_sourceNormalization {N : ℕ} {α t c L Csrc D : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hα : |α| < 1 / 2)
    (hc : 0 < c) (hL : 0 < L) (hD : 0 ≤ D) (hCsrc : 0 ≤ Csrc)
    (hsource : D ≤ Csrc * zetaCompensatedPrimeForm N α t)
    (hfloor : c * L ^ 6 * α ^ 2 ≤ D)
    (hQ : 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (twistedMoment N α 0) ^ 2)
      < c * L ^ 6) :
    α = 0 := by
  set S := twistedMoment N α 0 with hS
  set K : ℝ := 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * S ^ 2) with hK
  have hcL : 0 < c * L ^ 6 := by positivity
  have hprime := zetaCompensatedPrimeForm_le hN hα t
  have hsrc : D ≤ K * α ^ 2 := by
    have := mul_le_mul_of_nonneg_left hprime hCsrc
    have hrw : Csrc * (120000 * (Real.log N) ^ 2 * α ^ 2 * t ^ 2 * S ^ 2) = K * α ^ 2 := by
      rw [hK]; ring
    linarith [hsource, this, hrw.le, hrw.ge]
  have heta : K / (c * L ^ 6) < 1 := (div_lt_one hcL).mpr hQ
  have hKnn : 0 ≤ K := by
    rw [hK]; positivity
  have hcontract : D ≤ K / (c * L ^ 6) * D := by
    have hstep : K / (c * L ^ 6) * (c * L ^ 6 * α ^ 2) ≤ K / (c * L ^ 6) * D :=
      mul_le_mul_of_nonneg_left hfloor (by positivity)
    have heq : K / (c * L ^ 6) * (c * L ^ 6 * α ^ 2) = K * α ^ 2 := by
      field_simp
    linarith [hsrc, hstep, heq.le, heq.ge]
  exact offLineTarget_excluded_of_relative_budget hc hL hD heta hfloor hcontract

/-- The same decision, phrased with the source ratio `Q`. -/
theorem offLineZero_excluded_of_sourceRatio {N : ℕ} {α t c L Csrc D : ℝ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) (hα : |α| < 1 / 2)
    (hc : 0 < c) (hL : 0 < L) (hD : 0 ≤ D) (hCsrc : 0 ≤ Csrc)
    (hsource : D ≤ Csrc * zetaCompensatedPrimeForm N α t)
    (hfloor : c * L ^ 6 * α ^ 2 ≤ D)
    (hQ : 120000 * (Real.log N) ^ 2 * sourceRatio N α t Csrc L < c) :
    α = 0 := by
  refine offLineZero_excluded_of_sourceNormalization hN hα hc hL hD hCsrc hsource hfloor ?_
  have hL6 : 0 < L ^ 6 := by positivity
  rw [sourceRatio] at hQ
  rw [div_eq_mul_inv, ← mul_assoc] at hQ
  have := (mul_lt_mul_iff_of_pos_right hL6).mpr hQ
  calc 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (twistedMoment N α 0) ^ 2)
      = 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (twistedMoment N α 0) ^ 2)
        * (L ^ 6)⁻¹ * L ^ 6 := by field_simp
    _ < c * L ^ 6 := this

/-- **The necessary side of the same comparison.**  Whatever the cutoff or the
rearrangement, the prime side is bounded *below* by an absolute multiple of
`C_src t² S₀²` in the small-phase regime, provided the source identification is
an equality-type lower bound.  So a contraction cannot be obtained by improving
the prime estimate: only a small source normalization can produce it. -/
theorem primeSide_ge_of_sourceNormalization {N : ℕ} {α t Csrc : ℝ}
    (hN : (10 : ℝ) ^ 9 ≤ (N : ℝ)) (hα : |α| < 1 / 2) (ht : |t| * Real.log N ≤ 1)
    (hCsrc : 0 ≤ Csrc) :
    Csrc * (t ^ 2 / (2 * 10 ^ 7) * (twistedMoment N α 0) ^ 2)
      ≤ Csrc * zetaAnchoredPrimeForm N α t :=
  mul_le_mul_of_nonneg_left (zetaAnchoredPrimeForm_ge hN hα ht) hCsrc


/-! ### The matching lower bound: the compensated prime observable is not small

The upper bound `zetaCompensatedPrimeForm_le` is only half of the decision.  If
the compensated prime observable could be much *smaller* than `α²t²S₀²`, the
route would still have room.  It cannot: the next theorems bound it below by an
absolute multiple of the same quantity, so the whole comparison really is a
comparison of the source normalization with the Gram floor. -/

/-- `x²/2 ≤ cosh x − 1`: the exact quadratic lower bound for the twist. -/
theorem half_sq_le_cosh_sub_one (x : ℝ) : x ^ 2 / 2 ≤ Real.cosh x - 1 := by
  have h2 : Real.cosh x = 1 + 2 * Real.sinh (x / 2) ^ 2 := by
    have h := Real.cosh_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring] at h
    nlinarith [Real.cosh_sq (x / 2)]
  have hs : (x / 2) ^ 2 ≤ Real.sinh (x / 2) ^ 2 := by
    rcases le_total 0 x with hx | hx
    · have h := Real.self_le_sinh_iff.mpr (show 0 ≤ x / 2 by linarith)
      nlinarith [h]
    · have h := Real.sinh_le_self_iff.mpr (show x / 2 ≤ 0 by linarith)
      nlinarith [h]
  nlinarith [hs, h2]

/-- The pair version: `cosh x cosh y − 1 ≥ (x² + y²)/2`. -/
theorem coshProd_sub_one_ge (x y : ℝ) :
    x ^ 2 / 2 + y ^ 2 / 2 ≤ Real.cosh x * Real.cosh y - 1 := by
  have hx := half_sq_le_cosh_sub_one x
  have hy := half_sq_le_cosh_sub_one y
  have h1 : (1 : ℝ) ≤ Real.cosh x := Real.one_le_cosh x
  have h2 : (1 : ℝ) ≤ Real.cosh y := Real.one_le_cosh y
  nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]

/-- **Cauchy–Schwarz for pair sums.**  For nonnegative pair coefficients,
`(∑∑ a u)² ≤ (∑∑ a)(∑∑ a u²)`. -/
theorem sq_pairSum_le {s : Finset ℕ} {a u : ℕ → ℕ → ℝ}
    (ha : ∀ n ∈ s, ∀ m ∈ s, 0 ≤ a n m) :
    (∑ n ∈ s, ∑ m ∈ s, a n m * u n m) ^ 2
      ≤ (∑ n ∈ s, ∑ m ∈ s, a n m) * (∑ n ∈ s, ∑ m ∈ s, a n m * (u n m) ^ 2) := by
  classical
  have key := Finset.sum_mul_sq_le_sq_mul_sq (s ×ˢ s)
    (fun p : ℕ × ℕ => Real.sqrt (a p.1 p.2))
    (fun p : ℕ × ℕ => Real.sqrt (a p.1 p.2) * u p.1 p.2)
  have h1 : ∑ p ∈ s ×ˢ s, Real.sqrt (a p.1 p.2) * (Real.sqrt (a p.1 p.2) * u p.1 p.2)
      = ∑ n ∈ s, ∑ m ∈ s, a n m * u n m := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
    rw [← mul_assoc, Real.mul_self_sqrt (ha n hn m hm)]
  have h2 : ∑ p ∈ s ×ˢ s, Real.sqrt (a p.1 p.2) ^ 2 = ∑ n ∈ s, ∑ m ∈ s, a n m := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
    rw [Real.sq_sqrt (ha n hn m hm)]
  have h3 : ∑ p ∈ s ×ˢ s, (Real.sqrt (a p.1 p.2) * u p.1 p.2) ^ 2
      = ∑ n ∈ s, ∑ m ∈ s, a n m * (u n m) ^ 2 := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun m hm => ?_
    rw [mul_pow, Real.sq_sqrt (ha n hn m hm)]
  rw [h1, h2, h3] at key
  exact key

/-- The untwisted pair mass is the square of the untwisted prime mass. -/
theorem pairSum_vonMangoldt (N : ℕ) :
    ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, coshVonMangoldt 0 n * coshVonMangoldt 0 m
      = (twistedMoment N 0 0) ^ 2 := by
  rw [twistedMoment_zero, sq, Finset.sum_mul]
  exact Finset.sum_congr rfl fun n _ => by rw [Finset.mul_sum]

/-- **The fourth-moment lower bound.**  The compensated prime observable
dominates `α²t²/4` times the fourth log-difference moment of the untwisted von
Mangoldt weights, in the small-phase regime. -/
theorem zetaCompensatedPrimeForm_ge_quartic {N : ℕ} {α t : ℝ}
    (ht : |t| * Real.log N ≤ 1) :
    α ^ 2 * t ^ 2 / 4 *
        (∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, coshVonMangoldt 0 n * coshVonMangoldt 0 m *
          ((Real.log n - Real.log m) ^ 2) ^ 2)
      ≤ zetaCompensatedPrimeForm N α t := by
  have hsplit : zetaCompensatedPrimeForm N α t
      = ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N,
          (coshVonMangoldt α n * coshVonMangoldt α m *
              (1 - Real.cos (t * (Real.log n - Real.log m)))
            - coshVonMangoldt 0 n * coshVonMangoldt 0 m *
              (1 - Real.cos (t * (Real.log n - Real.log m)))) := by
    unfold zetaCompensatedPrimeForm zetaAnchoredPrimeForm pairForm
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by rw [← Finset.sum_sub_distrib]
  have hlhs : α ^ 2 * t ^ 2 / 4 *
      (∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, coshVonMangoldt 0 n * coshVonMangoldt 0 m *
        ((Real.log n - Real.log m) ^ 2) ^ 2)
      = ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, α ^ 2 * t ^ 2 / 4 *
          (coshVonMangoldt 0 n * coshVonMangoldt 0 m *
            ((Real.log n - Real.log m) ^ 2) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [Finset.mul_sum]
  rw [hsplit, hlhs]
  refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => ?_
  have hLn : 0 ≤ Λ n := vonMangoldt_nonneg
  have hLm : 0 ≤ Λ m := vonMangoldt_nonneg
  have hLL : 0 ≤ Λ n * Λ m := mul_nonneg hLn hLm
  have hphase := zeta_phase_le ht n hn m hm
  have hcosl : (t * (Real.log n - Real.log m)) ^ 2 / 4
      ≤ 1 - Real.cos (t * (Real.log n - Real.log m)) := quarter_sq_le_one_sub_cos hphase
  have htw := coshProd_sub_one_ge (2 * α * Real.log n) (2 * α * Real.log m)
  have hquad : α ^ 2 * (Real.log n - Real.log m) ^ 2
      ≤ Real.cosh (2 * α * Real.log n) * Real.cosh (2 * α * Real.log m) - 1 := by
    nlinarith [htw, sq_nonneg (Real.log n - Real.log m), sq_nonneg α,
      sq_nonneg (Real.log n + Real.log m), sq_nonneg (α * (Real.log n + Real.log m))]
  have hcos0 : 0 ≤ 1 - Real.cos (t * (Real.log n - Real.log m)) := by
    have := Real.cos_le_one (t * (Real.log n - Real.log m)); linarith
  have hstep : Λ n * Λ m * (α ^ 2 * (Real.log n - Real.log m) ^ 2) *
      ((t * (Real.log n - Real.log m)) ^ 2 / 4)
      ≤ Λ n * Λ m *
        (Real.cosh (2 * α * Real.log n) * Real.cosh (2 * α * Real.log m) - 1) *
        (1 - Real.cos (t * (Real.log n - Real.log m))) := by
    have h1 : Λ n * Λ m * (α ^ 2 * (Real.log n - Real.log m) ^ 2)
        ≤ Λ n * Λ m *
          (Real.cosh (2 * α * Real.log n) * Real.cosh (2 * α * Real.log m) - 1) :=
      mul_le_mul_of_nonneg_left hquad hLL
    have h2 : 0 ≤ Λ n * Λ m * (α ^ 2 * (Real.log n - Real.log m) ^ 2) := by positivity
    have h3 : 0 ≤ (t * (Real.log n - Real.log m)) ^ 2 / 4 := by positivity
    nlinarith [h1, h2, h3, hcosl, hcos0]
  simp only [coshVonMangoldt, mul_zero, zero_mul, Real.cosh_zero, mul_one]
  nlinarith [hstep]

/-- **The literal compensated prime observable, bounded below.**  For the actual
cosh-twisted von Mangoldt weights, in the small-phase regime,

```
10⁻¹⁴ α² t² ψ(N)²  ≤  𝒟_N(α,t),
```

where `ψ(N) = S₀(0)` is the untwisted prime mass.  Together with
`zetaCompensatedPrimeForm_le` the compensated prime observable is pinned to
`α²t²S₀²` within absolute constants (and a factor `(log N)²`). -/
theorem zetaCompensatedPrimeForm_ge {N : ℕ} (hN : (10 : ℝ) ^ 9 ≤ (N : ℝ)) {α t : ℝ}
    (ht : |t| * Real.log N ≤ 1) :
    (1 / 10 ^ 14 : ℝ) * α ^ 2 * t ^ 2 * (twistedMoment N 0 0) ^ 2
      ≤ zetaCompensatedPrimeForm N α t := by
  have hN8 : (10 : ℝ) ^ 8 ≤ (N : ℝ) := le_trans (by norm_num) hN
  set S : ℝ := twistedMoment N 0 0 with hS
  -- the untwisted mass is positive
  have hSpos : 0 < S := by
    have hmass := (twistedPrimeMass hN8 (α := (0 : ℝ)) (by norm_num)).1
    have hrw : (N : ℝ) ^ (1 + 2 * |(0 : ℝ)|) = (N : ℝ) := by
      simp [Real.rpow_one]
    rw [hrw] at hmass
    have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 9]
    have : 0 < (N : ℝ) / 32 := by positivity
    exact lt_of_lt_of_le this hmass
  -- the second log-difference moment of the untwisted weights
  have hvar : (2 : ℝ) * (1 / 10 ^ 7) * S ^ 2
      ≤ ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, coshVonMangoldt 0 n * coshVonMangoldt 0 m *
          (Real.log n - Real.log m) ^ 2 := by
    have hlow := zetaTwistedPrimeVariance_lower hN (α := (0 : ℝ)) (by norm_num)
    have hid := varForm_eq_double (Icc 1 N) (coshVonMangoldt 0) (fun n => Real.log n)
    have hlv : logVar (Icc 1 N) (coshVonMangoldt 0) (fun n => Real.log n)
        = twistedMoment N 0 0 * twistedMoment N 0 2 - (twistedMoment N 0 1) ^ 2 :=
      logVar_icc_eq N 0
    unfold logVar at hlv
    rw [hid] at hlv
    rw [hS]
    linarith [hlow, hlv]
  -- Cauchy–Schwarz upgrades it to the fourth moment
  have hCS := sq_pairSum_le (s := Icc 1 N)
    (a := fun n m => coshVonMangoldt 0 n * coshVonMangoldt 0 m)
    (u := fun n m => (Real.log n - Real.log m) ^ 2)
    (fun n _ m _ => mul_nonneg (coshVonMangoldt_nonneg 0 n) (coshVonMangoldt_nonneg 0 m))
  rw [pairSum_vonMangoldt N] at hCS
  have hS2 : (0 : ℝ) < S ^ 2 := by positivity
  have hquartic : (4 : ℝ) / 10 ^ 14 * S ^ 2
      ≤ ∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, coshVonMangoldt 0 n * coshVonMangoldt 0 m *
          ((Real.log n - Real.log m) ^ 2) ^ 2 := by
    have hsq : ((2 : ℝ) * (1 / 10 ^ 7) * S ^ 2) ^ 2
        ≤ (∑ n ∈ Icc 1 N, ∑ m ∈ Icc 1 N, coshVonMangoldt 0 n * coshVonMangoldt 0 m *
            (Real.log n - Real.log m) ^ 2) ^ 2 := by
      have hnn : (0 : ℝ) ≤ 2 * (1 / 10 ^ 7) * S ^ 2 := by positivity
      nlinarith [hvar, hnn]
    have hSS : S ^ 2 = (twistedMoment N 0 0) ^ 2 := by rw [hS]
    rw [← hSS] at hCS
    nlinarith [hCS, hsq, hS2]
  have hmain := zetaCompensatedPrimeForm_ge_quartic (N := N) (α := α) (t := t) ht
  have hfac : (0 : ℝ) ≤ α ^ 2 * t ^ 2 / 4 := by positivity
  have := mul_le_mul_of_nonneg_left hquartic hfac
  linarith [hmain, this]

/-- **The negative half of the decision.**  Suppose the literal anchored defect
is of the geometric size `D ≤ K L⁶α²`, and the source normalization is *large*:

```
K L⁶  ≤  C_src · 10⁻¹⁴ t² ψ(N)².
```

Then the compensated prime term alone is at least the whole defect, so the
relative budget it produces has `η ≥ 1` and **cannot** be contractive.  Together
with `offLineZero_excluded_of_sourceNormalization`, this makes the size of the
source normalization the binary decision point of the route. -/
theorem primeBudget_not_contractive {N : ℕ} {α t K L Csrc D : ℝ}
    (hN : (10 : ℝ) ^ 9 ≤ (N : ℝ)) (ht : |t| * Real.log N ≤ 1) (hCsrc : 0 ≤ Csrc)
    (hD : D ≤ K * L ^ 6 * α ^ 2)
    (hbig : K * L ^ 6 ≤ Csrc * ((1 / 10 ^ 14 : ℝ) * t ^ 2 * (twistedMoment N 0 0) ^ 2)) :
    D ≤ Csrc * zetaCompensatedPrimeForm N α t := by
  have hlow := zetaCompensatedPrimeForm_ge hN (α := α) (t := t) ht
  have hmul := mul_le_mul_of_nonneg_left hlow hCsrc
  have hα2 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
  have hstep : K * L ^ 6 * α ^ 2
      ≤ Csrc * ((1 / 10 ^ 14 : ℝ) * t ^ 2 * (twistedMoment N 0 0) ^ 2) * α ^ 2 :=
    mul_le_mul_of_nonneg_right hbig hα2
  nlinarith [hD, hmul, hstep]


/-! ### What the source normalization must be

In the route's own normalization the geometric scale is the log-length of the
prime truncation, `L = log N`.  Substituting the computed prime side into the
contraction condition determines the size the source constant `C_src` must have,
and the answer is unambiguous: it must decay like `1/N`. -/

/-- `(log N)⁴ ≤ 256 N`. -/
theorem log_pow_four_le (N : ℕ) : (Real.log N) ^ 4 ≤ 256 * (N : ℝ) := by
  have h := Real.log_natCast_le_rpow_div N (ε := 1 / 4) (by norm_num)
  have hnn : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hx : ((N : ℝ) ^ ((1 : ℝ) / 4)) ^ 4 = (N : ℝ) := by
    rw [← Real.rpow_natCast ((N : ℝ) ^ ((1 : ℝ) / 4)) 4,
      ← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  have h256 : ((1 : ℝ) / 4) ^ 4 = 1 / 256 := by norm_num
  have hstep : ((N : ℝ) ^ ((1 : ℝ) / 4) / (1 / 4)) ^ 4 = 256 * (N : ℝ) := by
    rw [div_pow, hx, h256]
    field_simp
  calc (Real.log N) ^ 4 ≤ ((N : ℝ) ^ ((1 : ℝ) / 4) / (1 / 4)) ^ 4 := by
        exact pow_le_pow_left₀ hnn h 4
    _ = 256 * (N : ℝ) := hstep

/-- **The forced scale of the source normalization.**  If the contraction
condition of `offLineZero_excluded_of_sourceNormalization` holds in the route's
own normalization `L = log N`, then

```
C_src · t² · N  <  3c.
```

So the source normalization is not free: it has to supply a factor of order
`1/N` — i.e. of order `1/S₀`, exactly the division by the prime mass that G13
identified as the only remaining place the missing factor could live. -/
theorem sourceNormalization_forced_scale {N : ℕ} (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ))
    {c t Csrc : ℝ} (hc : 0 < c) (hCsrc : 0 ≤ Csrc)
    (hQ : 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (twistedMoment N 0 0) ^ 2)
        < c * (Real.log N) ^ 6) :
    Csrc * t ^ 2 * (N : ℝ) < 3 * c := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hN1 : (1 : ℝ) < (N : ℝ) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 10) 8]
  have hLpos : 0 < Real.log N := Real.log_pos hN1
  have hmass := (twistedPrimeMass hN (α := (0 : ℝ)) (by norm_num)).1
  have hrw : (N : ℝ) ^ (1 + 2 * |(0 : ℝ)|) = (N : ℝ) := by simp [Real.rpow_one]
  rw [hrw] at hmass
  have hSsq : (N : ℝ) ^ 2 / 1024 ≤ (twistedMoment N 0 0) ^ 2 := by
    have hnn : (0 : ℝ) ≤ (N : ℝ) / 32 := by positivity
    nlinarith [hmass, hnn]
  have hct : 0 ≤ Csrc * t ^ 2 := by positivity
  have hL2 : 0 < (Real.log N) ^ 2 := by positivity
  have hlow : 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * ((N : ℝ) ^ 2 / 1024))
      ≤ 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (twistedMoment N 0 0) ^ 2) := by
    have := mul_le_mul_of_nonneg_left hSsq hct
    nlinarith [this, hL2]
  have hL4 := log_pow_four_le N
  have hkey : Csrc * t ^ 2 * (N : ℝ) ^ 2 * 120000 / 1024 < c * (Real.log N) ^ 4 := by
    have hchain : 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * ((N : ℝ) ^ 2 / 1024))
        < c * (Real.log N) ^ 6 := lt_of_le_of_lt hlow hQ
    have hL6 : c * (Real.log N) ^ 6 = c * (Real.log N) ^ 4 * (Real.log N) ^ 2 := by ring
    rw [hL6] at hchain
    have hrewrite : 120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * ((N : ℝ) ^ 2 / 1024))
        = (Csrc * t ^ 2 * (N : ℝ) ^ 2 * 120000 / 1024) * (Real.log N) ^ 2 := by ring
    rw [hrewrite] at hchain
    exact lt_of_mul_lt_mul_right (by linarith [hchain]) (le_of_lt hL2)
  nlinarith [hkey, hL4, hct, hN0, hc]

/-- **No fixed source normalization can work.**  For any strictly positive
constant `C_src` and any nonzero shift `t`, the contraction condition fails as
soon as `N ≥ 3c/(C_src t²)`.  There is no asymptotics here and no limit: the
threshold is explicit. -/
theorem contraction_condition_fails_of_fixed_normalization {N : ℕ}
    (hN : (10 : ℝ) ^ 8 ≤ (N : ℝ)) {c t Csrc : ℝ} (hc : 0 < c) (hCsrc : 0 ≤ Csrc)
    (hbig : 3 * c ≤ Csrc * t ^ 2 * (N : ℝ)) :
    ¬ (120000 * (Real.log N) ^ 2 * (Csrc * t ^ 2 * (twistedMoment N 0 0) ^ 2)
        < c * (Real.log N) ^ 6) := by
  intro hQ
  have := sourceNormalization_forced_scale hN hc hCsrc hQ
  linarith

end RiemannAnalytic
