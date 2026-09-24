/-
# The integrated phase payment for the Waleffe amplitude, over the reals

The Round 105 Agda lane composes three facts on a rational bookkeeping carrier:

* a *pointwise* comparison of adverse critical production with the viscous
  phase damping of the triad amplitude, `ν P ≤ 2 γ A₊`, with
  `γ = ν(r_k²+r_p²+r_q²)`;
* the *positive-part (Kato) integration* of the scalar damped–forced amplitude
  equation `Ȧ = −γA + F`, giving `A₊(t₁) + γ∫A₊ ≤ A₊(t₀) + ∫F₊`;
* a finite summation over adverse cells.

This file proves all three over `ℝ`, from genuine calculus, so that the Round
105 reduction is available as an analytic theorem rather than as an arithmetic
record:

  `ν ∑_τ ∫_{t₀}^{t₁} P_τ ≤ 2 ∑_τ A_τ₊(t₀) + 2 ∑_τ ∫_{t₀}^{t₁} (F_τ)₊`.

The Kato step is proved by the exact Duhamel comparison (integrating factor,
monotonicity of `L − e^{γ(t−t₀)}A`, and one application of the fundamental
theorem of calculus to `−e^{−γ(t−t₀)}L`); no differentiation of `max(·,0)` is
needed and no smallness or sign hypothesis on `A` or `F` is used.

The right-hand side is exactly the quantity whose cutoff-uniform bound is the
open Round 105 wall (`PhysicalWeightedPositiveWaleffeNetworkForcingBudget`);
see `WaleffeNetworkForcingBudget.lean`.
-/
import Mathlib

open MeasureTheory

noncomputable section

namespace ClayNS.Waleffe

/-- **Reverse triangle inequality on a triad.**  If `k + p + q = 0`, the
difference of the two majority radii is at most the third radius.  This is the
Round 105 "minority-radius seam", proved here for genuine vectors. -/
theorem triad_reverse_triangle {E : Type*} [SeminormedAddCommGroup E] {k p q : E}
    (h : k + p + q = 0) : ‖q‖ - ‖p‖ ≤ ‖k‖ := by
  have hq : q = -(k + p) := by linear_combination (norm := abel) h
  have h2 : ‖q‖ ≤ ‖k‖ + ‖p‖ := by
    rw [hq, norm_neg]
    exact norm_add_le _ _
  linarith

/-- **Pointwise phase-damping payment.**  On an adverse mixed-helicity cell with
minority radius `r_k`, the Round 102 production `P = 2 r_k (r_q − r_p) A` is
dominated by twice the viscous phase damping `γ A`, `γ = ν(r_k²+r_p²+r_q²)`.
Only the reverse-triangle bound `r_q − r_p ≤ r_k` and nonnegativity are used. -/
theorem phase_damping_payment {nu rk rp rq amp : ℝ} (hnu : 0 ≤ nu) (hamp : 0 ≤ amp)
    (hrk : 0 ≤ rk) (htri : rq - rp ≤ rk) :
    nu * (2 * rk * (rq - rp) * amp) ≤ 2 * (nu * (rk ^ 2 + rp ^ 2 + rq ^ 2)) * amp := by
  have h1 : rk * (rq - rp) ≤ rk * rk := by nlinarith
  nlinarith [sq_nonneg rp, sq_nonneg rq, mul_nonneg hnu hamp]

/-- **Kato / Duhamel integrated positive-part balance** for the scalar damped–
forced amplitude equation `Ȧ = −γ A + F` with constant damping rate `γ ≥ 0`:

  `A₊(t₁) + γ ∫_{t₀}^{t₁} A₊ ≤ A₊(t₀) + ∫_{t₀}^{t₁} F₊`.

No sign hypothesis on `A` or `F` is used. -/
theorem kato_integrated_payment {A F : ℝ → ℝ} {gam t₀ t₁ : ℝ}
    (hgam : 0 ≤ gam) (ht : t₀ ≤ t₁) (hF : Continuous F)
    (hA : ∀ t, HasDerivAt A (-gam * A t + F t) t) :
    max (A t₁) 0 + gam * ∫ t in t₀..t₁, max (A t) 0
      ≤ max (A t₀) 0 + ∫ t in t₀..t₁, max (F t) 0 := by
  have hAd : Differentiable ℝ A := fun t => (hA t).differentiableAt
  have hAc : Continuous A := hAd.continuous
  set Fp : ℝ → ℝ := fun t => max (F t) 0 with hFp
  have hFpc : Continuous Fp := hF.max continuous_const
  set w : ℝ → ℝ := fun t => Real.exp (gam * (t - t₀)) with hw
  have hwc : Continuous w := by rw [hw]; fun_prop
  have hwpos : ∀ t, 0 < w t := fun _ => Real.exp_pos _
  have hwd : ∀ t, HasDerivAt w (gam * w t) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => gam * (s - t₀)) gam t := by
      simpa using ((hasDerivAt_id t).sub_const t₀).const_mul gam
    simpa [hw, mul_comm] using h1.exp
  have hintc : Continuous (fun s => w s * Fp s) := hwc.mul hFpc
  set L : ℝ → ℝ := fun t => max (A t₀) 0 + ∫ s in t₀..t, w s * Fp s with hL
  have hLd : ∀ t, HasDerivAt L (w t * Fp t) t := by
    intro t
    have h := intervalIntegral.integral_hasDerivAt_right
      (hintc.intervalIntegrable t₀ t)
      (hintc.stronglyMeasurableAtFilter _ _) hintc.continuousAt
    simpa [hL] using h.const_add (max (A t₀) 0)
  have hLdiff : Differentiable ℝ L := fun t => (hLd t).differentiableAt
  have hLc : Continuous L := hLdiff.continuous
  set g : ℝ → ℝ := fun t => w t * A t with hg
  have hgd : ∀ t, HasDerivAt g (w t * F t) t := by
    intro t
    have h := (hwd t).mul (hA t)
    convert h using 1
    ring
  have hDd : ∀ t, HasDerivAt (fun s => L s - g s) (w t * Fp t - w t * F t) t :=
    fun t => (hLd t).sub (hgd t)
  have hDmono : Monotone (fun s => L s - g s) := by
    apply monotone_of_deriv_nonneg (fun t => (hDd t).differentiableAt)
    intro t
    rw [(hDd t).deriv]
    have : F t ≤ Fp t := le_max_left _ _
    nlinarith [hwpos t]
  have hLt₀ : L t₀ = max (A t₀) 0 := by simp [hL]
  have hwt₀ : w t₀ = 1 := by simp [hw]
  have hD0 : 0 ≤ L t₀ - g t₀ := by
    simp only [hg, hwt₀, hLt₀, one_mul]
    exact sub_nonneg.mpr (le_max_left _ _)
  have hkey : ∀ t, t₀ ≤ t → g t ≤ L t := by
    intro t htt
    have h := hDmono htt
    simp only at h
    linarith [hD0, h]
  -- the decaying comparison function
  set e : ℝ → ℝ := fun t => Real.exp (-(gam * (t - t₀))) with he
  have hec : Continuous e := by rw [he]; fun_prop
  have hepos : ∀ t, 0 < e t := fun _ => Real.exp_pos _
  have hew : ∀ t, e t * w t = 1 := by
    intro t; rw [he, hw, ← Real.exp_add]; simp
  have hed : ∀ t, HasDerivAt e (-gam * e t) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -(gam * (s - t₀))) (-gam) t := by
      simpa using (((hasDerivAt_id t).sub_const t₀).const_mul gam).neg
    simpa [he, mul_comm] using h1.exp
  have hLnn : ∀ t, t₀ ≤ t → 0 ≤ L t := by
    intro t htt
    rw [hL]
    have h1 : (0:ℝ) ≤ ∫ s in t₀..t, w s * Fp s := by
      apply intervalIntegral.integral_nonneg htt
      intro s _
      exact mul_nonneg (hwpos s).le (by rw [hFp]; exact le_max_right _ _)
    simp only
    linarith [le_max_right (A t₀) (0:ℝ)]
  have hApos : ∀ t, t₀ ≤ t → max (A t) 0 ≤ e t * L t := by
    intro t htt
    have h1 : A t ≤ e t * L t := by
      have h2 := hkey t htt
      rw [hg] at h2
      have h4 := mul_le_mul_of_nonneg_left h2 (hepos t).le
      calc A t = e t * (w t * A t) := by rw [← mul_assoc, hew t, one_mul]
        _ ≤ e t * L t := h4
    exact max_le h1 (mul_nonneg (hepos t).le (hLnn t htt))
  have hPhi : ∀ t, HasDerivAt (fun s => -(e s * L s)) (gam * (e t * L t) - Fp t) t := by
    intro t
    have h := ((hed t).mul (hLd t)).neg
    convert h using 1
    have hh : e t * (w t * Fp t) = Fp t := by rw [← mul_assoc, hew t, one_mul]
    nlinarith [hh]
  have hcont : Continuous (fun t => gam * (e t * L t) - Fp t) := by fun_prop
  have hFTC : ∫ t in t₀..t₁, (gam * (e t * L t) - Fp t) = -(e t₁ * L t₁) - -(e t₀ * L t₀) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hPhi x)
      (hcont.intervalIntegrable _ _)
  have hsplit : ∫ t in t₀..t₁, (gam * (e t * L t) - Fp t)
      = gam * (∫ t in t₀..t₁, e t * L t) - ∫ t in t₀..t₁, Fp t := by
    have hi1 : IntervalIntegrable (fun t => gam * (e t * L t)) volume t₀ t₁ :=
      ((continuous_const.mul (hec.mul hLc)) :
        Continuous fun t => gam * (e t * L t)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable Fp volume t₀ t₁ := hFpc.intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul]
  have hmono2 : (∫ t in t₀..t₁, max (A t) 0) ≤ ∫ t in t₀..t₁, e t * L t := by
    apply intervalIntegral.integral_mono_on ht
      ((hAc.max continuous_const).intervalIntegrable _ _)
      ((hec.mul hLc).intervalIntegrable _ _)
    intro s hs
    exact hApos s hs.1
  have hAt₁ : max (A t₁) 0 ≤ e t₁ * L t₁ := hApos t₁ ht
  have het₀ : e t₀ = 1 := by rw [he]; simp
  have hgi : gam * (∫ t in t₀..t₁, max (A t) 0) ≤ gam * ∫ t in t₀..t₁, e t * L t :=
    mul_le_mul_of_nonneg_left hmono2 hgam
  rw [het₀, hLt₀, hsplit] at hFTC
  linarith

/-- **Cell-level integrated production payment.**  Combining the pointwise phase
damping bound with the Kato balance: the time-integrated adverse production of
one triad is paid by its initial positive amplitude and by the integral of the
positive part of its network forcing. -/
theorem cell_integrated_production_payment {A F P : ℝ → ℝ} {nu gam t₀ t₁ : ℝ}
    (hgam : 0 ≤ gam) (ht : t₀ ≤ t₁) (hF : Continuous F) (hP : Continuous P)
    (hA : ∀ t, HasDerivAt A (-gam * A t + F t) t)
    (hpay : ∀ t, nu * P t ≤ 2 * gam * max (A t) 0) :
    nu * ∫ t in t₀..t₁, P t ≤ 2 * max (A t₀) 0 + 2 * ∫ t in t₀..t₁, max (F t) 0 := by
  have hAdiff : Differentiable ℝ A := fun t => (hA t).differentiableAt
  have hAc : Continuous A := hAdiff.continuous
  have h1 : nu * ∫ t in t₀..t₁, P t = ∫ t in t₀..t₁, nu * P t :=
    (intervalIntegral.integral_const_mul _ _).symm
  have h2 : (∫ t in t₀..t₁, nu * P t) ≤ ∫ t in t₀..t₁, 2 * gam * max (A t) 0 := by
    apply intervalIntegral.integral_mono_on ht
      ((continuous_const.mul hP).intervalIntegrable _ _)
      ((continuous_const.mul (hAc.max continuous_const)).intervalIntegrable _ _)
    intro s _
    exact hpay s
  have h3 : (∫ t in t₀..t₁, 2 * gam * max (A t) 0) = 2 * (gam * ∫ t in t₀..t₁, max (A t) 0) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    congr 1
    funext t
    ring
  have h4 := kato_integrated_payment hgam ht hF hA
  have h5 : (0:ℝ) ≤ max (A t₁) 0 := le_max_right _ _
  rw [h1]
  rw [h3] at h2
  linarith

/-- **Finite summation over adverse cells.**  Nothing beyond additivity: if
every cell pays, the network pays. -/
theorem finite_production_payment {ι : Type*} (s : Finset ι) (nu : ℝ)
    (P Ainit Fpos : ι → ℝ)
    (h : ∀ i ∈ s, nu * P i ≤ 2 * Ainit i + 2 * Fpos i) :
    nu * ∑ i ∈ s, P i ≤ 2 * ∑ i ∈ s, Ainit i + 2 * ∑ i ∈ s, Fpos i := by
  have h1 : nu * ∑ i ∈ s, P i = ∑ i ∈ s, nu * P i := Finset.mul_sum _ _ _
  have h2 : ∑ i ∈ s, nu * P i ≤ ∑ i ∈ s, (2 * Ainit i + 2 * Fpos i) :=
    Finset.sum_le_sum h
  have h3 : ∑ i ∈ s, (2 * Ainit i + 2 * Fpos i)
      = 2 * ∑ i ∈ s, Ainit i + 2 * ∑ i ∈ s, Fpos i := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [h1]
  linarith

end ClayNS.Waleffe
