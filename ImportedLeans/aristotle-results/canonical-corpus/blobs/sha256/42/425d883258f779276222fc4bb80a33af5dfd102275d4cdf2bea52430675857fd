/-
# G20 — the pole/error autopsy of the literal explicit-formula prime side

G18 (`LiteralSourceIdentity.lean`) showed that the literal Riemann–Weil
transport is *linear* in the prime data while the anchored Gram observable is
*quadratic*; G19 (`NormalizedTransverseResidual.lean`) removed the last two
escapes (a common normalization is invisible to a relative gate, and the literal
prime interface is cosine-only, so an odd taper exposes a sine channel of the
same size).  What was left after G19 is a single arithmetic statement: the
literal transported residual

```
S(x_v) − β S(x_u),      S(x) = ∑_{n ≤ N} Λ(n) n^{-1/2} cos(x log n),
```

has natural size `N^{1/2}`, whereas the zero-side witness only supplies the
polylogarithmic scale `L²|α|`.

This module is the **autopsy**, not another rescue attempt.  It subtracts the
deterministic (prime-number-theorem) pole contribution *exactly*, and then
measures what is left.

## 1.  `S = M + E`, with `E` an honest prime-discrepancy functional

`weilPoleMainTerm N x = ∫_1^N t^{-1/2} cos(x log t) dt` is the continuum main
term and `weilPoleErrorTerm N x = S(x) − M(x)`.  The content is
`weilPrimeSum_pole_error_decomposition` together with
`weilPoleErrorTerm_eq_discrepancyFunctional`: Abel summation against `Λ`
(Mathlib's `sum_mul_eq_sub_sub_integral_mul'`) plus integration by parts for the
continuum term gives, with `f_x(t) = t^{-1/2}cos(x log t)`,

```
E(x) = f_x(N)·(ψ(N) − N) + 1 − ∫_1^N f_x'(t)·(ψ(t) − t) dt.
```

So `E` is *literally* a linear functional of the Chebyshev discrepancy
`ψ(t) − t` — nothing about it is heuristic.

## 2.  Does the projection coefficient cancel the pole term?

`transverseResidual_mainTermDecision`: the residual main term
`M(x_v) − β M(x_u)` vanishes **iff** `β` equals the single number
`M(x_v)/M(x_u)`, and otherwise its size is exactly
`|M(x_u)|·|β − M(x_v)/M(x_u)|`.  Cancellation is one scalar condition on `β`,
not an identity supplied by the geometry.  At the literal anchor used in G19
(`x_u = x_v = 0`, where `M(N,0) = 2(√N − 1)` exactly,
`weilPoleMainTerm_zero_freq`) the projection coefficient that the Gram geometry
produces is `β ≠ 1` and then
`transverseResidual_mainTerm_atAnchor_lowerBound` gives
`|M_v − β M_u| ≥ |1 − β|·√N`: **red before any prime cancellation**
(`transverseResidual_atAnchor_red`).

## 3.  What a green gate would have to prove about `ψ(t) − t`

`transverseResidual_error_requiredScale`: a green gate on the *literal*
transported residual `weilGridResidualPrimeSum` forces

```
|M(x_v) − β M(x_u)| − c_r (log N)²/4  ≤  |E(x_v) − β E(x_u)|,
```

and, in the only surviving branch (exact pole cancellation),

```
|E(x_v) − β E(x_u)| ≤ c_r (log N)²/4 .
```

The two calibration theorems say what that costs.
`weilDiscrepancyFunctional_abs_le_of_sqrt_bound`: a square-root-strength
discrepancy `|ψ(t) − t| ≤ K√t` *does* give `|E(x)| ≤ K + 1 + K(1/2+|x|)log N`,
i.e. polylogarithmic — exactly the required scale.
`weilDiscrepancyFunctional_model_lower`: for a model discrepancy
`R(t) = K t^θ` with `θ > 1/2` — which is all that PNT-strength (or any
`θ > 1/2` zero-free-region) input permits — the same functional is at least
`K N^{θ−1/2}`, which is not polylogarithmic; and
`modelDiscrepancy_exceeds_gateScale` turns that into a threshold statement:
beyond an explicit `N₀` such a profile exceeds the gate scale `c_r(log N)²/4`
outright.  So the surviving branch needs a discrepancy estimate of essentially
square-root strength: an RH-strength input.

The one remaining escape — forcing cancellation by running the two frequencies
together — is closed as well: at `x_u = x_v` the pole term cancels only at
`β = 1` (`transverseResidual_mainTerm_equalFrequencies_iff`), where the literal
transported residual is identically zero
(`weilGridResidualPrimeSum_degenerate`) and the zero-side floor collapses to
`L²|α| = 0` (`transverseResidual_degenerate_source_collapse`): no witness is
left.

## 4.  The no-go

`gramExplicitFormulaRouteNoGo`: under the literal source architecture every
green gate satisfies the dichotomy — either the deterministic pole term fails to
cancel (route dead at the main term) or the gate *is* a polylogarithmic bound on
the literal Chebyshev-discrepancy functional.  Either way the closure theorem
must supply an independently deep prime-discrepancy estimate; the explicit
formula does not supply one.

Nothing here proves the Riemann Hypothesis, nothing here weakens
`RiemannHypothesisFor`, and no `sorry`, `axiom`, postulate, Boolean receipt or
numerical evidence appears.
-/
import RiemannAnalytic.NormalizedTransverseResidual

open Finset Real ArithmeticFunction MeasureTheory

namespace RiemannAnalytic

/-! ## 0.  The continuum kernel `f_x(t) = t^{-1/2} cos(x log t)` and its derivative -/

/-- The continuum kernel of the literal prime transport:
`f_x(t) = t^{-1/2} cos(x log t)`. -/
noncomputable def weilPoleKernel (x t : ℝ) : ℝ :=
  t ^ (-(1 / 2) : ℝ) * Real.cos (x * Real.log t)

/-- The derivative of `weilPoleKernel x` on `t > 0`:
`f_x'(t) = −t^{-3/2}((1/2)cos(x log t) + x sin(x log t))`. -/
noncomputable def weilPoleKernelDeriv (x t : ℝ) : ℝ :=
  -(t ^ (-(3 / 2) : ℝ)) * ((1 / 2) * Real.cos (x * Real.log t) + x * Real.sin (x * Real.log t))

theorem weilPoleKernel_one (x : ℝ) : weilPoleKernel x 1 = 1 := by
  unfold weilPoleKernel; simp

theorem weilPoleKernel_zero_freq {t : ℝ} : weilPoleKernel 0 t = t ^ (-(1 / 2) : ℝ) := by
  unfold weilPoleKernel; simp

theorem weilPoleKernelDeriv_zero_freq {t : ℝ} :
    weilPoleKernelDeriv 0 t = -(t ^ (-(3 / 2) : ℝ)) * (1 / 2) := by
  unfold weilPoleKernelDeriv; simp

/-- `f_x` is differentiable on the positive axis, with the stated derivative. -/
theorem hasDerivAt_weilPoleKernel (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (weilPoleKernel x) (weilPoleKernelDeriv x t) t := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ (-(1 / 2) : ℝ)) ((-(1 / 2)) * t ^ (-(1 / 2) - 1 : ℝ)) t :=
    Real.hasDerivAt_rpow_const (Or.inl ht.ne')
  have hlog : HasDerivAt (fun s : ℝ => x * Real.log s) (x * (1 / t)) t := by
    simpa using (Real.hasDerivAt_log ht.ne').const_mul x
  have h2 : HasDerivAt (fun s : ℝ => Real.cos (x * Real.log s))
      (-Real.sin (x * Real.log t) * (x * (1 / t))) t := hlog.cos
  refine (h1.mul h2).congr_deriv ?_
  have e1 : t ^ (-(1 / 2) - 1 : ℝ) = t ^ (-(3 / 2) : ℝ) := by norm_num
  have e2 : t ^ (-(1 / 2) : ℝ) * (1 / t) = t ^ (-(3 / 2) : ℝ) := by
    rw [show (-(3 / 2) : ℝ) = -(1 / 2) - 1 by norm_num, Real.rpow_sub ht]
    simp [div_eq_mul_inv]
  unfold weilPoleKernelDeriv
  rw [e1]
  linear_combination (-x * Real.sin (x * Real.log t)) * e2

theorem continuousAt_weilPoleKernel (x : ℝ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (weilPoleKernel x) t := by
  have h1 : ContinuousAt (fun s : ℝ => s ^ (-(1 / 2) : ℝ)) t :=
    Real.continuousAt_rpow_const t _ (Or.inl ht.ne')
  have hl : ContinuousAt (fun s : ℝ => x * Real.log s) t :=
    continuousAt_const.mul (Real.continuousAt_log ht.ne')
  exact h1.mul (Real.continuous_cos.continuousAt.comp hl)

theorem continuousAt_weilPoleKernelDeriv (x : ℝ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (weilPoleKernelDeriv x) t := by
  have h1 : ContinuousAt (fun s : ℝ => s ^ (-(3 / 2) : ℝ)) t :=
    Real.continuousAt_rpow_const t _ (Or.inl ht.ne')
  have hl : ContinuousAt (fun s : ℝ => x * Real.log s) t :=
    continuousAt_const.mul (Real.continuousAt_log ht.ne')
  have hc : ContinuousAt (fun s : ℝ => Real.cos (x * Real.log s)) t :=
    Real.continuous_cos.continuousAt.comp hl
  have hs : ContinuousAt (fun s : ℝ => Real.sin (x * Real.log s)) t :=
    Real.continuous_sin.continuousAt.comp hl
  exact h1.neg.mul ((continuousAt_const.mul hc).add (continuousAt_const.mul hs))

theorem continuousOn_weilPoleKernelDeriv (x b : ℝ) :
    ContinuousOn (weilPoleKernelDeriv x) (Set.Icc (1 : ℝ) b) :=
  fun _ ht => (continuousAt_weilPoleKernelDeriv x (lt_of_lt_of_le one_pos ht.1)).continuousWithinAt

/-- The pointwise size of the kernel derivative: `|f_x'(t)| ≤ (1/2 + |x|) t^{-3/2}`. -/
theorem weilPoleKernelDeriv_abs_le (x : ℝ) {t : ℝ} (ht : 0 < t) :
    |weilPoleKernelDeriv x t| ≤ (1 / 2 + |x|) * t ^ (-(3 / 2) : ℝ) := by
  have hp : (0 : ℝ) < t ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos ht _
  have hfac : |(1 / 2) * Real.cos (x * Real.log t) + x * Real.sin (x * Real.log t)|
      ≤ 1 / 2 + |x| := by
    have h1 : |(1 / 2 : ℝ) * Real.cos (x * Real.log t)| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
      have := Real.abs_cos_le_one (x * Real.log t)
      nlinarith [abs_nonneg (Real.cos (x * Real.log t))]
    have h2 : |x * Real.sin (x * Real.log t)| ≤ |x| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg x) (Real.abs_sin_le_one _)
    exact le_trans (abs_add_le _ _) (by linarith)
  unfold weilPoleKernelDeriv
  rw [abs_mul, abs_neg, abs_of_pos hp]
  calc t ^ (-(3 / 2) : ℝ)
        * |(1 / 2) * Real.cos (x * Real.log t) + x * Real.sin (x * Real.log t)|
      ≤ t ^ (-(3 / 2) : ℝ) * (1 / 2 + |x|) := mul_le_mul_of_nonneg_left hfac hp.le
    _ = (1 / 2 + |x|) * t ^ (-(3 / 2) : ℝ) := by ring

/-! ## 1.  The literal plateau prime sum, the main term, and the error term -/

/-- The literal plateau prime sum
`S(x) = ∑_{n ≤ N} Λ(n) n^{-1/2} cos(x log n)`: this is exactly half of the
literal transported quantity `weilGridPrimeSum φ N x` on a plateau taper. -/
noncomputable def weilPlateauPrimeSum (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 1 N, Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) * Real.cos (x * Real.log n)

/-- On a plateau taper the literal Weil grid prime sum is `2 S(x)`. -/
theorem weilGridPrimeSum_eq_two_mul_plateau {φ : ℝ → ℝ} {N : ℕ} (x : ℝ)
    (hplat : ∀ n ∈ Icc 1 N, φ (Real.log n) = 1) :
    weilGridPrimeSum φ N x = 2 * weilPlateauPrimeSum N x := by
  unfold weilGridPrimeSum weilPlateauPrimeSum
  congr 1
  exact Finset.sum_congr rfl fun n hn => by rw [hplat n hn]; ring

/-- On a plateau taper the literal transported residual is `2 (S(x_v) − β S(x_u))`. -/
theorem weilGridResidualPrimeSum_eq_two_mul_plateau {φ : ℝ → ℝ} {N : ℕ} (β xu xv : ℝ)
    (hplat : ∀ n ∈ Icc 1 N, φ (Real.log n) = 1) :
    weilGridResidualPrimeSum φ N β xu xv
      = 2 * (weilPlateauPrimeSum N xv - β * weilPlateauPrimeSum N xu) := by
  rw [weilGridResidualPrimeSum_eq, weilGridPrimeSum_eq_two_mul_plateau xv hplat,
    weilGridPrimeSum_eq_two_mul_plateau xu hplat]
  ring

/-- The continuum (prime-number-theorem pole) main term
`M(x) = ∫_1^N t^{-1/2} cos(x log t) dt`. -/
noncomputable def weilPoleMainTerm (N : ℕ) (x : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..(N : ℝ), weilPoleKernel x t

/-- The prime discrepancy part of the literal prime sum: `E(x) = S(x) − M(x)`. -/
noncomputable def weilPoleErrorTerm (N : ℕ) (x : ℝ) : ℝ :=
  weilPlateauPrimeSum N x - weilPoleMainTerm N x

/-- **`weilPrimeSum_pole_error_decomposition` — `S = M + E`.**  The literal
plateau prime sum splits exactly into the deterministic continuum pole
contribution `M(x) = ∫_1^N t^{-1/2}cos(x log t)dt` and the prime discrepancy
`E(x)`.  (`weilPoleErrorTerm_eq_discrepancyFunctional` identifies `E` as a
literal functional of `ψ(t) − t`.) -/
theorem weilPrimeSum_pole_error_decomposition (N : ℕ) (x : ℝ) :
    weilPlateauPrimeSum N x = weilPoleMainTerm N x + weilPoleErrorTerm N x := by
  unfold weilPoleErrorTerm; ring

/-- At zero frequency the main term is exactly `2(√N − 1)`. -/
theorem weilPoleMainTerm_zero_freq {N : ℕ} (hN : 1 ≤ N) :
    weilPoleMainTerm N 0 = 2 * (Real.sqrt N - 1) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hne : ((0 : ℝ)) ∉ Set.uIcc (1 : ℝ) (N : ℝ) := by
    rw [Set.uIcc_of_le hNR]
    intro h
    linarith [h.1]
  unfold weilPoleMainTerm
  rw [show (fun t : ℝ => weilPoleKernel 0 t) = fun t : ℝ => t ^ (-(1 / 2) : ℝ) from
    funext fun t => weilPoleKernel_zero_freq]
  rw [integral_rpow (Or.inr ⟨by norm_num, hne⟩)]
  rw [show (-(1 / 2) + 1 : ℝ) = 1 / 2 by norm_num, Real.one_rpow, ← Real.sqrt_eq_rpow]
  ring

/-! ## 2.  Abel summation: `E` is a literal functional of the Chebyshev discrepancy -/

/-- Mathlib's Abel-summation partial sums `∑_{k ≤ ⌊t⌋} Λ(k)` are the Chebyshev
function `ψ(t)`. -/
theorem sum_Icc_vonMangoldt_eq_psi (t : ℝ) : ∑ k ∈ Icc 0 ⌊t⌋₊, Λ k = Chebyshev.psi t := by
  unfold Chebyshev.psi
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons]
  simp

/-- The Chebyshev discrepancy `R(t) = ψ(t) − t`. -/
noncomputable def chebyshevDiscrepancy (t : ℝ) : ℝ := Chebyshev.psi t - t

/-- **Abel summation for the literal plateau prime sum.** -/
theorem weilPlateauPrimeSum_abel {N : ℕ} (hN : 1 ≤ N) (x : ℝ) :
    weilPlateauPrimeSum N x
      = weilPoleKernel x N * Chebyshev.psi (N : ℝ)
        - ∫ t in (1 : ℝ)..(N : ℝ), weilPoleKernelDeriv x t * Chebyshev.psi t := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hderiv : ∀ t ∈ Set.Icc (1 : ℝ) (N : ℝ),
      deriv (weilPoleKernel x) t = weilPoleKernelDeriv x t :=
    fun t ht => (hasDerivAt_weilPoleKernel x (lt_of_lt_of_le one_pos ht.1)).deriv
  have hdiff : ∀ t ∈ Set.Icc ((1 : ℕ) : ℝ) ((N : ℕ) : ℝ), DifferentiableAt ℝ (weilPoleKernel x) t := by
    intro t ht
    simp only [Nat.cast_one] at ht
    exact (hasDerivAt_weilPoleKernel x (lt_of_lt_of_le one_pos ht.1)).differentiableAt
  have hcont : ContinuousOn (weilPoleKernelDeriv x) (Set.Icc (1 : ℝ) (N : ℝ)) :=
    continuousOn_weilPoleKernelDeriv x _
  have hint : IntegrableOn (deriv (weilPoleKernel x)) (Set.Icc ((1 : ℕ) : ℝ) ((N : ℕ) : ℝ)) := by
    simp only [Nat.cast_one]
    exact hcont.integrableOn_Icc.congr_fun (fun t ht => (hderiv t ht).symm) measurableSet_Icc
  have key := sum_mul_eq_sub_sub_integral_mul' (fun n : ℕ => (Λ n : ℝ))
    (f := weilPoleKernel x) hN hdiff hint
  simp only [Nat.cast_one] at key
  rw [show (∑ k ∈ Icc 0 1, (Λ k : ℝ)) = 0 by
        rw [show (Icc 0 1 : Finset ℕ) = {0, 1} by decide]
        simp [ArithmeticFunction.vonMangoldt_apply_one]] at key
  have hsumN : (∑ k ∈ Icc 0 N, (Λ k : ℝ)) = Chebyshev.psi (N : ℝ) := by
    have h := sum_Icc_vonMangoldt_eq_psi (N : ℝ)
    rwa [Nat.floor_natCast] at h
  rw [hsumN] at key
  have hlhs : ∑ k ∈ Ioc 1 N, weilPoleKernel x k * (Λ k : ℝ) = weilPlateauPrimeSum N x := by
    unfold weilPlateauPrimeSum weilPoleKernel
    rw [show (Icc 1 N : Finset ℕ) = insert 1 (Ioc 1 N) by
          rw [Finset.Icc_eq_cons_Ioc hN]; simp]
    rw [Finset.sum_insert (by simp),
      show (Λ 1 : ℝ) = 0 from by simp [ArithmeticFunction.vonMangoldt_apply_one]]
    simp only [zero_mul, zero_add]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hintegral : ∫ t in Set.Ioc (1 : ℝ) (N : ℝ), deriv (weilPoleKernel x) t
        * ∑ k ∈ Icc 0 ⌊t⌋₊, (Λ k : ℝ)
      = ∫ t in (1 : ℝ)..(N : ℝ), weilPoleKernelDeriv x t * Chebyshev.psi t := by
    rw [intervalIntegral.integral_of_le hNR]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [hderiv t ⟨ht.1.le, ht.2⟩, sum_Icc_vonMangoldt_eq_psi]
  rw [hlhs, hintegral] at key
  linarith [key]

/-- Integration by parts for the continuum main term. -/
theorem weilPoleMainTerm_byParts {N : ℕ} (hN : 1 ≤ N) (x : ℝ) :
    weilPoleMainTerm N x
      = weilPoleKernel x N * (N : ℝ) - 1 - ∫ t in (1 : ℝ)..(N : ℝ), weilPoleKernelDeriv x t * t := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have huIcc : Set.uIcc (1 : ℝ) (N : ℝ) = Set.Icc (1 : ℝ) (N : ℝ) := Set.uIcc_of_le hNR
  have hu : ∀ t ∈ Set.uIcc (1 : ℝ) (N : ℝ),
      HasDerivAt (weilPoleKernel x) (weilPoleKernelDeriv x t) t := by
    intro t ht
    rw [huIcc] at ht
    exact hasDerivAt_weilPoleKernel x (lt_of_lt_of_le one_pos ht.1)
  have hv : ∀ t ∈ Set.uIcc (1 : ℝ) (N : ℝ), HasDerivAt (fun s : ℝ => s) (1 : ℝ) t :=
    fun t _ => hasDerivAt_id t
  have hu' : IntervalIntegrable (weilPoleKernelDeriv x) volume (1 : ℝ) (N : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hNR).mpr
      (continuousOn_weilPoleKernelDeriv x _).integrableOn_Icc
  have hv' : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (1 : ℝ) (N : ℝ) :=
    intervalIntegrable_const
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  simp only [mul_one] at key
  unfold weilPoleMainTerm
  rw [key, weilPoleKernel_one]

/-- `f_x' · ψ` is interval integrable on `[1,N]`. -/
theorem intervalIntegrable_weilPoleKernelDeriv_mul_psi {N : ℕ} (hN : 1 ≤ N) (x : ℝ) :
    IntervalIntegrable (fun t => weilPoleKernelDeriv x t * Chebyshev.psi t) volume 1 (N : ℝ) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hNR]
  have h := integrableOn_mul_sum_Icc (c := fun n : ℕ => (Λ n : ℝ)) (m := 0) (a := (1 : ℝ))
    (b := (N : ℝ)) (g := weilPoleKernelDeriv x) zero_le_one
    (continuousOn_weilPoleKernelDeriv x _).integrableOn_Icc
  exact h.congr_fun (fun t _ => by rw [sum_Icc_vonMangoldt_eq_psi]) measurableSet_Icc

/-- `f_x' · R` is interval integrable on `[1,N]` for `R(t) = ψ(t) − t`. -/
theorem intervalIntegrable_weilPoleKernelDeriv_mul_chebyshevDiscrepancy {N : ℕ} (hN : 1 ≤ N)
    (x : ℝ) :
    IntervalIntegrable (fun t => weilPoleKernelDeriv x t * chebyshevDiscrepancy t) volume 1
      (N : ℝ) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hI2 : IntervalIntegrable (fun t => weilPoleKernelDeriv x t * t) volume 1 (N : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hNR]
    exact ((continuousOn_weilPoleKernelDeriv x _).mul continuousOn_id).integrableOn_Icc
  refine ((intervalIntegrable_weilPoleKernelDeriv_mul_psi hN x).sub hI2).congr fun t _ => ?_
  unfold chebyshevDiscrepancy
  ring

/-- **The prime-discrepancy functional.**  For a discrepancy profile `R`,

```
D_N(x, R) = f_x(N)·R(N) + 1 − ∫_1^N f_x'(t) R(t) dt.
```
-/
noncomputable def weilDiscrepancyFunctional (N : ℕ) (x : ℝ) (R : ℝ → ℝ) : ℝ :=
  weilPoleKernel x N * R N + 1 - ∫ t in (1 : ℝ)..(N : ℝ), weilPoleKernelDeriv x t * R t

/-- **`E` is exactly the Chebyshev-discrepancy functional.**  After the exact
subtraction of the continuum pole term, what is left of the literal prime sum is
a linear functional of `ψ(t) − t` alone. -/
theorem weilPoleErrorTerm_eq_discrepancyFunctional {N : ℕ} (hN : 1 ≤ N) (x : ℝ) :
    weilPoleErrorTerm N x = weilDiscrepancyFunctional N x chebyshevDiscrepancy := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hI1 := intervalIntegrable_weilPoleKernelDeriv_mul_psi hN x
  have hI2 : IntervalIntegrable (fun t => weilPoleKernelDeriv x t * t) volume 1 (N : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hNR]
    exact ((continuousOn_weilPoleKernelDeriv x _).mul continuousOn_id).integrableOn_Icc
  have hsplit : (∫ t in (1 : ℝ)..(N : ℝ), weilPoleKernelDeriv x t * Chebyshev.psi t)
      - (∫ t in (1 : ℝ)..(N : ℝ), weilPoleKernelDeriv x t * t)
      = ∫ t in (1 : ℝ)..(N : ℝ), weilPoleKernelDeriv x t * chebyshevDiscrepancy t := by
    rw [← intervalIntegral.integral_sub hI1 hI2]
    exact intervalIntegral.integral_congr fun t _ => by unfold chebyshevDiscrepancy; ring
  unfold weilPoleErrorTerm weilDiscrepancyFunctional chebyshevDiscrepancy
  rw [weilPlateauPrimeSum_abel hN, weilPoleMainTerm_byParts hN]
  have := hsplit
  unfold chebyshevDiscrepancy at this
  linarith [this]

/-! ## 3.  The scale of the discrepancy functional -/

/-- **Square-root-strength discrepancy gives a polylogarithmic error term.**
If `|R(t)| ≤ K √t` on `[1,N]` — the RH-strength bound, up to logs — then
`|D_N(x,R)| ≤ K + 1 + K(1/2 + |x|) log N`. -/
theorem weilDiscrepancyFunctional_abs_le_of_sqrt_bound {N : ℕ} {K : ℝ} {R : ℝ → ℝ} (x : ℝ)
    (hN : 1 ≤ N)
    (hint : IntervalIntegrable (fun t => weilPoleKernelDeriv x t * R t) volume 1 (N : ℝ))
    (hR : ∀ t ∈ Set.Icc (1 : ℝ) (N : ℝ), |R t| ≤ K * t ^ (1 / 2 : ℝ)) :
    |weilDiscrepancyFunctional N x R| ≤ K + 1 + K * (1 / 2 + |x|) * Real.log N := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hNR
  -- boundary term
  have hbdry : |weilPoleKernel x N * R N| ≤ K := by
    have h1 : |weilPoleKernel x (N : ℝ)| ≤ (N : ℝ) ^ (-(1 / 2) : ℝ) := by
      unfold weilPoleKernel
      rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hN0.le _)]
      have := Real.abs_cos_le_one (x * Real.log N)
      nlinarith [Real.rpow_pos_of_pos hN0 (-(1 / 2) : ℝ), abs_nonneg (Real.cos (x * Real.log N))]
    have h2 : |R (N : ℝ)| ≤ K * (N : ℝ) ^ (1 / 2 : ℝ) := hR _ ⟨hNR, le_rfl⟩
    have hprod : (N : ℝ) ^ (-(1 / 2) : ℝ) * ((N : ℝ) ^ (1 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hN0]; norm_num
    calc |weilPoleKernel x (N : ℝ) * R (N : ℝ)|
        = |weilPoleKernel x (N : ℝ)| * |R (N : ℝ)| := abs_mul _ _
      _ ≤ (N : ℝ) ^ (-(1 / 2) : ℝ) * (K * (N : ℝ) ^ (1 / 2 : ℝ)) := by
          apply mul_le_mul h1 h2 (abs_nonneg _) (Real.rpow_nonneg hN0.le _)
      _ = K * ((N : ℝ) ^ (-(1 / 2) : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ)) := by ring
      _ = K := by rw [hprod, mul_one]
  -- integral term
  have hcomp : ∀ t ∈ Set.Icc (1 : ℝ) (N : ℝ),
      |weilPoleKernelDeriv x t * R t| ≤ K * (1 / 2 + |x|) * t⁻¹ := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht.1
    have h1 : |weilPoleKernelDeriv x t| ≤ (1 / 2 + |x|) * t ^ (-(3 / 2) : ℝ) :=
      weilPoleKernelDeriv_abs_le x ht0
    have h2 : |R t| ≤ K * t ^ (1 / 2 : ℝ) := hR t ht
    have hprod : t ^ (-(3 / 2) : ℝ) * t ^ (1 / 2 : ℝ) = t⁻¹ := by
      rw [← Real.rpow_add ht0]
      rw [show (-(3 / 2) + 1 / 2 : ℝ) = -1 by norm_num, Real.rpow_neg_one]
    calc |weilPoleKernelDeriv x t * R t| = |weilPoleKernelDeriv x t| * |R t| := abs_mul _ _
      _ ≤ ((1 / 2 + |x|) * t ^ (-(3 / 2) : ℝ)) * (K * t ^ (1 / 2 : ℝ)) := by
          refine mul_le_mul h1 h2 (abs_nonneg _) ?_
          positivity
      _ = K * (1 / 2 + |x|) * (t ^ (-(3 / 2) : ℝ) * t ^ (1 / 2 : ℝ)) := by ring
      _ = K * (1 / 2 + |x|) * t⁻¹ := by rw [hprod]
  have hbound : |∫ t in (1 : ℝ)..(N : ℝ), weilPoleKernelDeriv x t * R t|
      ≤ K * (1 / 2 + |x|) * Real.log N := by
    have hmono : |∫ t in (1 : ℝ)..(N : ℝ), weilPoleKernelDeriv x t * R t|
        ≤ ∫ t in (1 : ℝ)..(N : ℝ), K * (1 / 2 + |x|) * t⁻¹ := by
      have hconstint : IntervalIntegrable (fun t : ℝ => K * (1 / 2 + |x|) * t⁻¹) volume 1 (N : ℝ) :=
        ContinuousOn.intervalIntegrable_of_Icc hNR (continuousOn_const.mul
          (continuousOn_inv₀.mono fun t ht => ne_of_gt (lt_of_lt_of_le one_pos ht.1)))
      exact le_trans (intervalIntegral.abs_integral_le_integral_abs hNR)
        (intervalIntegral.integral_mono_on hNR hint.abs hconstint hcomp)
    have hlog : ∫ t in (1 : ℝ)..(N : ℝ), K * (1 / 2 + |x|) * t⁻¹
        = K * (1 / 2 + |x|) * Real.log N := by
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos hN0]
      simp
    linarith [hmono, hlog.le, hlog.ge]
  unfold weilDiscrepancyFunctional
  calc |weilPoleKernel x N * R N + 1 - ∫ t in (1 : ℝ)..(N : ℝ), weilPoleKernelDeriv x t * R t|
      ≤ |weilPoleKernel x N * R N| + |(1 : ℝ)|
        + |∫ t in (1 : ℝ)..(N : ℝ), weilPoleKernelDeriv x t * R t| := by
        have h := abs_add_le (weilPoleKernel x N * R N + 1)
          (-(∫ t in (1 : ℝ)..(N : ℝ), weilPoleKernelDeriv x t * R t))
        have h2 := abs_add_le (weilPoleKernel x N * R N) (1 : ℝ)
        rw [abs_neg] at h
        rw [sub_eq_add_neg]
        linarith
    _ ≤ K + 1 + K * (1 / 2 + |x|) * Real.log N := by
        rw [abs_one]; linarith

/-- **A discrepancy of exponent `θ > 1/2` is not polylogarithmic in the
functional.**  For the model profile `R(t) = K t^θ` — which is permitted by any
hypothesis weaker than square-root cancellation (in particular by every
classical PNT error term) — the functional at zero frequency is at least
`K N^{θ−1/2}`.  The inequality is proved for every exponent `θ`; its force is at
`θ > 1/2`, where `N^{θ−1/2}` outgrows every polylogarithm. -/
theorem weilDiscrepancyFunctional_model_lower {N : ℕ} {K θ : ℝ} (hN : 1 ≤ N) (hK : 0 ≤ K) :
    K * (N : ℝ) ^ (θ - 1 / 2 : ℝ)
      ≤ weilDiscrepancyFunctional N 0 (fun t => K * t ^ (θ : ℝ)) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hNR
  have hbdry : weilPoleKernel 0 (N : ℝ) * (K * (N : ℝ) ^ (θ : ℝ))
      = K * (N : ℝ) ^ (θ - 1 / 2 : ℝ) := by
    rw [weilPoleKernel_zero_freq, show (θ - 1 / 2 : ℝ) = -(1 / 2) + θ by ring,
      Real.rpow_add hN0]
    ring
  have hneg : ∀ t ∈ Set.Icc (1 : ℝ) (N : ℝ),
      weilPoleKernelDeriv 0 t * (K * t ^ (θ : ℝ)) ≤ 0 := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht.1
    rw [weilPoleKernelDeriv_zero_freq]
    have hnn : (0 : ℝ) ≤ t ^ (-(3 / 2) : ℝ) * (1 / 2) * (K * t ^ (θ : ℝ)) := by
      have h1 : (0 : ℝ) < t ^ (-(3 / 2) : ℝ) := Real.rpow_pos_of_pos ht0 _
      have h2 : (0 : ℝ) ≤ t ^ (θ : ℝ) := Real.rpow_nonneg ht0.le _
      positivity
    nlinarith
  have hintle : (∫ t in (1 : ℝ)..(N : ℝ), weilPoleKernelDeriv 0 t * (K * t ^ (θ : ℝ))) ≤ 0 := by
    by_cases hint : IntervalIntegrable (fun t => weilPoleKernelDeriv 0 t * (K * t ^ (θ : ℝ)))
      volume 1 (N : ℝ)
    · have h := intervalIntegral.integral_mono_on hNR hint
        (g := fun _ : ℝ => (0 : ℝ)) intervalIntegrable_const hneg
      simpa using h
    · rw [intervalIntegral.integral_undef hint]
  unfold weilDiscrepancyFunctional
  rw [hbdry]
  linarith

/-! ## 4.  The decisions -/

/-- **`transverseResidual_mainTermDecision` — does the projection coefficient
cancel the pole term?**  The residual main term vanishes exactly when `β` is the
single number `M(x_v)/M(x_u)`, and otherwise its modulus is exactly
`|M(x_u)|·|β − M(x_v)/M(x_u)|`.  Pole cancellation is one scalar condition on
`β`; the Gram geometry does not supply it. -/
theorem transverseResidual_mainTermDecision (N : ℕ) (xu xv β : ℝ)
    (hMu : weilPoleMainTerm N xu ≠ 0) :
    (weilPoleMainTerm N xv - β * weilPoleMainTerm N xu = 0
        ↔ β = weilPoleMainTerm N xv / weilPoleMainTerm N xu)
      ∧ |weilPoleMainTerm N xv - β * weilPoleMainTerm N xu|
          = |weilPoleMainTerm N xu| * |β - weilPoleMainTerm N xv / weilPoleMainTerm N xu| := by
  constructor
  · constructor
    · intro h
      field_simp
      linarith
    · intro h
      rw [h]
      field_simp
      ring
  · rw [← abs_mul, abs_sub_comm]
    congr 1
    field_simp

/-- **The literal anchor is red at the main term.**  At the degenerate anchor
`x_u = x_v = 0` used in G19, `M(N,0) = 2(√N − 1)`, so for a projection
coefficient `β ≠ 1` the deterministic pole contribution to the residual is at
least `|1 − β|√N` — it does **not** cancel. -/
theorem transverseResidual_mainTerm_atAnchor_lowerBound {N : ℕ} {β : ℝ} (hN : 4 ≤ N) :
    |1 - β| * Real.sqrt N ≤ |weilPoleMainTerm N 0 - β * weilPoleMainTerm N 0| := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have hNR : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsqrt : (2 : ℝ) ≤ Real.sqrt N := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt hNR
  rw [weilPoleMainTerm_zero_freq hN1]
  rw [show 2 * (Real.sqrt N - 1) - β * (2 * (Real.sqrt N - 1))
      = (1 - β) * (2 * (Real.sqrt N - 1)) by ring, abs_mul,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * (Real.sqrt N - 1))]
  have h : Real.sqrt N ≤ 2 * (Real.sqrt N - 1) := by linarith
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- **`transverseResidual_error_requiredScale` — what a green gate costs.**

Suppose the literal transported residual of G19 satisfies the gate
`|weilGridResidualPrimeSum φ N β x_u x_v| ≤ c_r L² |α|` for a plateau taper, an
admissible support length `L ≤ log N` and an off-line displacement
`|α| ≤ 1/2`.  Then

* the prime discrepancy must absorb the whole deterministic pole residual, up to
  the polylogarithmic gate scale, and
* in the only surviving branch — exact pole cancellation — the discrepancy
  combination itself is forced to be polylogarithmic.

By `weilDiscrepancyFunctional_abs_le_of_sqrt_bound` and
`weilDiscrepancyFunctional_model_lower`, the second bullet is an estimate of
essentially square-root (RH) strength for `ψ(t) − t`: a `θ > 1/2` discrepancy
profile produces `N^{θ−1/2}`, not a polylogarithm. -/
theorem transverseResidual_error_requiredScale {φ : ℝ → ℝ} {N : ℕ} {β xu xv cr L alpha : ℝ}
    (hN : 1 ≤ N) (hL : 0 ≤ L) (hLN : L ≤ Real.log N) (halpha : |alpha| ≤ 1 / 2) (hcr : 0 ≤ cr)
    (hplat : ∀ n ∈ Icc 1 N, φ (Real.log n) = 1)
    (hgate : |weilGridResidualPrimeSum φ N β xu xv| ≤ cr * L ^ 2 * |alpha|) :
    |weilPoleMainTerm N xv - β * weilPoleMainTerm N xu| - cr * (Real.log N) ^ 2 / 4
        ≤ |weilPoleErrorTerm N xv - β * weilPoleErrorTerm N xu|
      ∧ (weilPoleMainTerm N xv = β * weilPoleMainTerm N xu →
          |weilPoleErrorTerm N xv - β * weilPoleErrorTerm N xu| ≤ cr * (Real.log N) ^ 2 / 4) := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hNR
  -- the gate, transferred to the plateau prime sum
  have hgate' : |weilPlateauPrimeSum N xv - β * weilPlateauPrimeSum N xu|
      ≤ cr * (Real.log N) ^ 2 / 4 := by
    rw [weilGridResidualPrimeSum_eq_two_mul_plateau β xu xv hplat, abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] at hgate
    have hL2 : L ^ 2 ≤ (Real.log N) ^ 2 := by nlinarith
    have hstep : cr * L ^ 2 * |alpha| ≤ cr * (Real.log N) ^ 2 / 2 := by
      have h1 : cr * L ^ 2 ≤ cr * (Real.log N) ^ 2 := mul_le_mul_of_nonneg_left hL2 hcr
      nlinarith [abs_nonneg alpha, sq_nonneg L, mul_nonneg hcr (sq_nonneg L)]
    linarith
  have hsplit : weilPlateauPrimeSum N xv - β * weilPlateauPrimeSum N xu
      = (weilPoleMainTerm N xv - β * weilPoleMainTerm N xu)
        + (weilPoleErrorTerm N xv - β * weilPoleErrorTerm N xu) := by
    rw [weilPrimeSum_pole_error_decomposition N xv, weilPrimeSum_pole_error_decomposition N xu]
    ring
  constructor
  · have hM : weilPoleMainTerm N xv - β * weilPoleMainTerm N xu
        = (weilPlateauPrimeSum N xv - β * weilPlateauPrimeSum N xu)
          - (weilPoleErrorTerm N xv - β * weilPoleErrorTerm N xu) := by linarith [hsplit]
    have h : |weilPoleMainTerm N xv - β * weilPoleMainTerm N xu|
        ≤ |weilPlateauPrimeSum N xv - β * weilPlateauPrimeSum N xu|
          + |weilPoleErrorTerm N xv - β * weilPoleErrorTerm N xu| := by
      rw [hM, sub_eq_add_neg]
      exact le_trans (abs_add_le _ _) (by rw [abs_neg])
    linarith [hgate', h]
  · intro hcancel
    have hz : weilPoleMainTerm N xv - β * weilPoleMainTerm N xu = 0 := by rw [hcancel]; ring
    rw [hz, zero_add] at hsplit
    rw [← hsplit]
    exact hgate'

/-- **The literal anchor: red before any prime cancellation.**  At
`x_u = x_v = 0` with `β ≠ 1` the deterministic pole term does not cancel, so a
green gate would force the prime discrepancy alone to be as large as
`|1 − β|√N − c_r(log N)²/4`. -/
theorem transverseResidual_atAnchor_red {φ : ℝ → ℝ} {N : ℕ} {β cr L alpha : ℝ}
    (hN : 4 ≤ N) (hL : 0 ≤ L) (hLN : L ≤ Real.log N) (halpha : |alpha| ≤ 1 / 2) (hcr : 0 ≤ cr)
    (hplat : ∀ n ∈ Icc 1 N, φ (Real.log n) = 1)
    (hgate : |weilGridResidualPrimeSum φ N β 0 0| ≤ cr * L ^ 2 * |alpha|) :
    |1 - β| * Real.sqrt N - cr * (Real.log N) ^ 2 / 4
      ≤ |weilPoleErrorTerm N 0 - β * weilPoleErrorTerm N 0| := by
  have hN1 : 1 ≤ N := le_trans (by norm_num) hN
  have h1 := (transverseResidual_error_requiredScale (φ := φ) (N := N) (β := β) (xu := 0) (xv := 0)
    (cr := cr) (L := L) (alpha := alpha) hN1 hL hLN halpha hcr hplat hgate).1
  have h2 := transverseResidual_mainTerm_atAnchor_lowerBound (N := N) (β := β) hN
  linarith

/-- **A model discrepancy of exponent `θ > 1/2` breaks the gate scale outright.**
For every `K > 0`, `θ > 1/2` and gate constant `c_r ≥ 0` there is a threshold
beyond which the discrepancy functional of the profile `R(t) = K t^θ` exceeds
the polylogarithmic gate scale `c_r (log N)²/4`.  Combined with
`transverseResidual_error_requiredScale`, this is the precise sense in which the
surviving branch demands an estimate of essentially square-root strength for
`ψ(t) − t`. -/
theorem modelDiscrepancy_exceeds_gateScale {K θ cr : ℝ} (hK : 0 < K) (hθ : 1 / 2 < θ)
    (hcr : 0 ≤ cr) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      cr * (Real.log N) ^ 2 / 4
        < weilDiscrepancyFunctional N 0 (fun t => K * t ^ (θ : ℝ)) := by
  set d : ℝ := (θ - 1 / 2) / 2 with hd_def
  have hd : 0 < d := by rw [hd_def]; linarith
  set A : ℝ := (cr * (2 / d) ^ 2 / 4 + 1) / K with hA_def
  have hA0 : 0 ≤ A := by
    rw [hA_def]
    positivity
  refine ⟨1 + ⌈A ^ (1 / d)⌉₊, fun N hN₀ => ?_⟩
  have hN1 : 1 ≤ N := le_trans (Nat.le_add_right 1 _) hN₀
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le one_pos hNR
  have hceil : A ^ (1 / d) ≤ (N : ℝ) := by
    have h1 : ((1 + ⌈A ^ (1 / d)⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN₀
    have h2 : A ^ (1 / d) ≤ (⌈A ^ (1 / d)⌉₊ : ℝ) := Nat.le_ceil _
    push_cast at h1
    linarith
  have hpow : A ≤ (N : ℝ) ^ d := by
    have h1 : (A ^ (1 / d)) ^ d ≤ ((N : ℝ)) ^ d :=
      Real.rpow_le_rpow (Real.rpow_nonneg hA0 _) hceil hd.le
    rwa [← Real.rpow_mul hA0, one_div, inv_mul_cancel₀ hd.ne', Real.rpow_one] at h1
  have hpow0 : (0 : ℝ) < (N : ℝ) ^ d := Real.rpow_pos_of_pos hN0 _
  have hthresh : cr * (2 / d) ^ 2 / 4 < K * (N : ℝ) ^ d := by
    have h := mul_le_mul_of_nonneg_left hpow hK.le
    rw [hA_def] at h
    have : K * ((cr * (2 / d) ^ 2 / 4 + 1) / K) = cr * (2 / d) ^ 2 / 4 + 1 := by
      field_simp
    linarith [h, this.le, this.ge]
  have hlog : cr * (Real.log N) ^ 2 / 4 ≤ cr * (2 / d) ^ 2 / 4 * (N : ℝ) ^ d := by
    have h := log_pow_le_mul_rpow N (k := 2) (by norm_num) (δ := d) hd
    push_cast at h
    nlinarith [h, hcr, hpow0]
  have hmain : cr * (2 / d) ^ 2 / 4 * (N : ℝ) ^ d < K * (N : ℝ) ^ d * (N : ℝ) ^ d :=
    mul_lt_mul_of_pos_right hthresh hpow0
  have hsplit : K * (N : ℝ) ^ (θ - 1 / 2 : ℝ) = K * (N : ℝ) ^ d * (N : ℝ) ^ d := by
    rw [mul_assoc, ← Real.rpow_add hN0]
    congr 2
    rw [hd_def]; ring
  have hlow := weilDiscrepancyFunctional_model_lower (N := N) (K := K) (θ := θ) hN1 hK.le
  rw [hsplit] at hlow
  linarith

/-! ### The one degenerate escape, closed

The only way the pole term can cancel *without* a coincidence between the Gram
geometry and the ratio `M(x_v)/M(x_u)` is to run the two frequencies together,
`x_u = x_v`, where cancellation happens exactly at `β = 1`.  But there the whole
transported residual is identically zero and the zero-side witness collapses:
the transverse component of a vector against itself vanishes, so the source
floor forces `L²|α| = 0`. -/

/-- At coincident frequencies the deterministic pole term cancels **only** at the
degenerate projection coefficient `β = 1`. -/
theorem transverseResidual_mainTerm_equalFrequencies_iff {N : ℕ} {x β : ℝ}
    (hM : weilPoleMainTerm N x ≠ 0) :
    weilPoleMainTerm N x - β * weilPoleMainTerm N x = 0 ↔ β = 1 := by
  constructor
  · intro h
    have : (1 - β) * weilPoleMainTerm N x = 0 := by linarith [h]
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith [h1]
    · exact absurd h1 hM
  · intro h
    rw [h]
    ring

/-- At coincident frequencies and `β = 1` the literal transported residual is
identically zero: the lane carries no prime information at all. -/
theorem weilGridResidualPrimeSum_degenerate (φ : ℝ → ℝ) (N : ℕ) (x : ℝ) :
    weilGridResidualPrimeSum φ N 1 x x = 0 := by
  unfold weilGridResidualPrimeSum
  rw [Finset.sum_congr rfl fun n _ => (by ring :
    Λ n * (n : ℝ) ^ (-(1 / 2) : ℝ) * φ (Real.log n)
        * (Real.cos (x * Real.log n) - 1 * Real.cos (x * Real.log n)) = 0)]
  simp

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The transverse component of a vector against itself vanishes. -/
theorem transverseComp_self (u : E) (hu : u ≠ 0) : transverseComp u u = 0 := by
  have hn : (‖u‖ : ℝ) ^ 2 ≠ 0 := by
    simpa using pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  unfold transverseComp
  rw [real_inner_self_eq_norm_sq, div_self hn, one_smul, sub_self]

/-- **The degenerate escape has no zero-side witness.**  If the residual vector
is taken against the anchor itself — the configuration in which the pole term
cancels at coincident frequencies — the source floor of
`transverseResidual_source_lowerBound` collapses to `L²|α| = 0`: there is no
off-line displacement left to detect. -/
theorem transverseResidual_degenerate_source_collapse (u : E) (hu : u ≠ 0)
    {c L alpha Cu : ℝ} (hc : 0 < c) (hCu : 0 < Cu)
    (hfloor : c * L ^ 6 * alpha ^ 2 ≤ wedgeSq u u) (hanchor : ‖u‖ ^ 2 ≤ Cu * L ^ 2) :
    L ^ 2 * |alpha| = 0 := by
  have hlow := transverseResidual_source_lowerBound u u hu hc hCu hfloor hanchor
  rw [transverseComp_self u hu, norm_zero] at hlow
  have hs : 0 < Real.sqrt (c / Cu) := Real.sqrt_pos.mpr (by positivity)
  have hnn : (0 : ℝ) ≤ L ^ 2 * |alpha| := by positivity
  nlinarith [hlow, hs, hnn]

/-- **`gramExplicitFormulaRouteNoGo` — the packaged conclusion of G18–G20.**

Under the literal source architecture, every green gate on the transported
residual satisfies the dichotomy:

* either the deterministic pole contribution `M(x_v) − β M(x_u)` **fails to
  cancel** — and then the gate is already contradicted at the main term by
  `transverseResidual_error_requiredScale` (the discrepancy would have to
  reproduce a term of size `N^{1/2}`), or
* the pole term cancels exactly — and then the gate **is** a polylogarithmic
  bound on the literal Chebyshev-discrepancy functional
  `D_N(x, ψ(t) − t)`.

By `weilDiscrepancyFunctional_abs_le_of_sqrt_bound` such a bound follows from a
square-root-strength estimate for `ψ(t) − t`, and by
`weilDiscrepancyFunctional_model_lower` it fails for every discrepancy profile
of exponent `θ > 1/2`.  So any closure theorem along this route must supply an
independently deep prime-discrepancy estimate of essentially RH strength: the
explicit-formula/Gram interface supplies no such mechanism. -/
theorem gramExplicitFormulaRouteNoGo {φ : ℝ → ℝ} {N : ℕ} {β xu xv cr L alpha : ℝ}
    (hN : 1 ≤ N) (hL : 0 ≤ L) (hLN : L ≤ Real.log N) (halpha : |alpha| ≤ 1 / 2) (hcr : 0 ≤ cr)
    (hplat : ∀ n ∈ Icc 1 N, φ (Real.log n) = 1)
    (hgate : |weilGridResidualPrimeSum φ N β xu xv| ≤ cr * L ^ 2 * |alpha|) :
    weilPoleMainTerm N xv ≠ β * weilPoleMainTerm N xu
      ∨ |weilDiscrepancyFunctional N xv chebyshevDiscrepancy
          - β * weilDiscrepancyFunctional N xu chebyshevDiscrepancy|
        ≤ cr * (Real.log N) ^ 2 / 4 := by
  by_cases hcancel : weilPoleMainTerm N xv = β * weilPoleMainTerm N xu
  · right
    have h := (transverseResidual_error_requiredScale (φ := φ) hN hL hLN halpha hcr hplat hgate).2
      hcancel
    rwa [weilPoleErrorTerm_eq_discrepancyFunctional hN xv,
      weilPoleErrorTerm_eq_discrepancyFunctional hN xu] at h
  · exact Or.inl hcancel

end RiemannAnalytic
