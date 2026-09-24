/-
# The far-pressure kernel bill, paid by the record normalisation alone

`GaussianLerayTranslationNoGo` shows that the *global* Gaussian Calderón–Zygmund
estimate for the Leray projector is false: the Gaussian weight is exponentially
localised while the Leray pressure is nonlocal.  The replacement architecture is
the near/far split of the pressure,

  `P = (-Δ)^{-1}∂_i∂_j(χ_R V_iV_j) + (-Δ)^{-1}∂_i∂_j((1-χ_R)V_iV_j)`,

in which the far piece is *not* estimated by an operator norm but by an explicit
kernel tail: for `‖y‖ ≤ R/2` the Newtonian second-derivative kernel obeys
`|∇_y K(y-z)| ≲ ‖z‖^{-4}` uniformly for `‖z‖ ≥ R`, so the far pressure gradient
inside the similarity ball is controlled by

  `∫_{‖z‖ > R} ‖V(z)‖² / ‖y − z‖⁴ dz`.                                   (tail)

This file computes that bill exactly, and shows that it is paid *in full* by the
single Phase-1 inherited quantity `‖V‖_∞ ≤ 1`:

* `ClayNS.integral_tailKernel` — the exact value `∫_{ℝ³} 1_{‖z‖>R} ‖z‖^{-4} dz
  = 3·vol(B₁)/R` (that is, `4π/R`), computed in polar coordinates;
* `ClayNS.far_pressure_kernel_expenditure` — for every continuous
  record-normalised `V` (`‖V‖_∞ ≤ 1`) and every `y` in the half-ball
  `‖y‖ ≤ R/2`,

    `∫_{‖z‖>R} ‖V z‖² / ‖y − z‖⁴ dz ≤ 48·vol(B₁)/R`,

  with a constant that is explicit, dimensionally correct, and **independent of
  every norm of `V` other than the record normalisation**;
* `ClayNS.far_pressure_kernel_expenditure_tendsto` — the bill tends to `0` as the
  cut radius `R → ∞`.

So the far half of the localized pressure architecture costs `O(1/R)` and needs
no further inherited estimate.  The remaining pressure work is entirely the
*near* piece on `B_R`, where the Gaussian weight is comparable to a constant and
ordinary local Calderón–Zygmund theory is available.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.GaussianLerayTranslationNoGo

open MeasureTheory Set

noncomputable section

namespace ClayNS

set_option maxRecDepth 4000
set_option maxHeartbeats 1000000

/-! ## The kernel tail -/

/-- The radial tail kernel `1_{‖x‖>R}·‖x‖^{-4}`: the exact decay of the gradient of the
Newtonian second-derivative kernel `∂_i∂_j(-Δ)^{-1}` at distance `‖x‖`. -/
def tailKernel (R : ℝ) (x : E3) : ℝ := if R < ‖x‖ then ‖x‖ ^ (-4:ℝ) else 0

lemma tailKernel_nonneg (R : ℝ) (x : E3) : 0 ≤ tailKernel R x := by
  rw [tailKernel]
  split
  · positivity
  · exact le_refl 0

/-- Polar reduction of the tail kernel: on `(0,∞)` the polar integrand `r²·1_{r>R}r^{-4}`
is exactly `1_{r>R}r^{-2}`. -/
lemma tail_polar_eqOn (R : ℝ) :
    Set.EqOn (fun y : ℝ => y ^ (3-1) • (if R < y then y ^ (-4:ℝ) else 0))
      (Set.indicator (Ioi R) (fun t : ℝ => t ^ (-2:ℝ))) (Ioi 0) := by
  intro y hy
  simp only [mem_Ioi] at hy
  by_cases h : R < y
  · simp only [if_pos h, Set.indicator_of_mem (show y ∈ Ioi R from h), smul_eq_mul]
    rw [show ((3:ℕ)-1) = 2 from rfl, ← Real.rpow_natCast y 2, ← Real.rpow_add hy]
    norm_num
  · simp only [if_neg h, smul_zero]
    exact (Set.indicator_of_notMem h _).symm

lemma integrable_tailKernel {R : ℝ} (hR : 0 < R) : Integrable (tailKernel R) := by
  have hiff := MeasureTheory.integrable_fun_norm_addHaar (E := E3) (F := ℝ) volume
    (f := fun t => if R < t then t ^ (-4:ℝ) else 0)
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  rw [hdim] at hiff
  refine hiff.mpr ?_
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-2:ℝ)) (Ioi R) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hR
  have hind0 : Integrable (Set.indicator (Ioi R) (fun t : ℝ => t ^ (-2:ℝ))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hbase
  exact (hind0.integrableOn).congr_fun (tail_polar_eqOn R).symm measurableSet_Ioi

/-- **The exact kernel tail.**  `∫_{‖z‖>R} ‖z‖^{-4} dz = 3·vol(B₁)/R = 4π/R`. -/
theorem integral_tailKernel {R : ℝ} (hR : 0 < R) :
    (∫ x : E3, tailKernel R x) = 3 * nsBallVol / R := by
  have hpolar := MeasureTheory.integral_fun_norm_addHaar (E := E3) (F := ℝ) volume
    (fun t => if R < t then t ^ (-4:ℝ) else 0)
  have hdim : Module.finrank ℝ E3 = 3 := by simp
  rw [hdim] at hpolar
  have hinner : (∫ y in Ioi (0:ℝ), y ^ (3-1) • (if R < y then y ^ (-4:ℝ) else 0)) = 1/R := by
    rw [setIntegral_congr_fun measurableSet_Ioi (tail_polar_eqOn R),
      setIntegral_indicator measurableSet_Ioi]
    have hset : Ioi (0:ℝ) ∩ Ioi R = Ioi R := by
      ext t
      simp only [mem_inter_iff, mem_Ioi]
      exact ⟨fun h => h.2, fun h => ⟨lt_trans hR h, h⟩⟩
    rw [hset, integral_Ioi_rpow_of_lt (by norm_num) hR,
      show (-2:ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
    norm_num
  simp only [tailKernel]
  rw [hpolar, hinner, nsBallVol]
  simp only [smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

/-! ## The far-pressure bill -/

/-- **`FarPressureKernelExpenditure`.**

For a record-normalised profile (`‖V‖_∞ ≤ 1`) and any base point `y` in the half-ball
`‖y‖ ≤ R/2`, the far part of the Leray pressure kernel integral is bounded by an explicit
`O(1/R)` constant:

  `∫_{‖z‖>R} ‖V z‖² / ‖y − z‖⁴ dz ≤ 48·vol(B₁)/R`.

The only property of `V` used is the record normalisation itself: no Dirichlet energy, no
`L^p` bound, no decay hypothesis.  This is what makes the near/far replacement of the (false)
global Gaussian Calderón–Zygmund estimate viable — the nonlocal half of the pressure is
already paid by Phase-1 inherited data. -/
theorem far_pressure_kernel_expenditure {R : ℝ} (hR : 0 < R) {V : E3 → E3}
    (hVc : Continuous V) (hV : ∀ z, ‖V z‖ ≤ 1) {y : E3} (hy : ‖y‖ ≤ R/2) :
    (∫ z : E3, (if R < ‖z‖ then ‖V z‖ ^ 2 / ‖y - z‖ ^ 4 else 0)) ≤ 48 * nsBallVol / R := by
  have hmeas : Measurable (fun z : E3 => if R < ‖z‖ then ‖V z‖ ^ 2 / ‖y - z‖ ^ 4 else 0) := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_lt measurable_const continuous_norm.measurable
    · exact ((hVc.norm.pow 2).measurable).div
        ((continuous_const.sub continuous_id).norm.pow 4).measurable
  have hpt : ∀ z : E3, (if R < ‖z‖ then ‖V z‖ ^ 2 / ‖y - z‖ ^ 4 else 0)
      ≤ 16 * tailKernel R z := by
    intro z
    rw [tailKernel]
    by_cases h : R < ‖z‖
    · rw [if_pos h, if_pos h]
      have hz : (0:ℝ) < ‖z‖ := lt_trans hR h
      have hd : ‖z‖ / 2 ≤ ‖y - z‖ := by
        have h1 : ‖z‖ - ‖y‖ ≤ ‖y - z‖ := by
          rw [norm_sub_rev]; exact norm_sub_norm_le _ _
        linarith
      have hd0 : (0:ℝ) < ‖z‖ / 2 := by linarith
      have hpow : (‖z‖ / 2) ^ 4 ≤ ‖y - z‖ ^ 4 := pow_le_pow_left₀ hd0.le hd 4
      have hV1 : ‖V z‖ ^ 2 ≤ 1 := by
        have := hV z; nlinarith [norm_nonneg (V z)]
      have hrp : ‖z‖ ^ (-4:ℝ) = (‖z‖ ^ 4)⁻¹ := by
        rw [show (-4:ℝ) = -((4:ℕ):ℝ) by norm_num, Real.rpow_neg hz.le, Real.rpow_natCast]
      rw [hrp]
      have hyz4 : (0:ℝ) < ‖y - z‖ ^ 4 := lt_of_lt_of_le (by positivity) hpow
      rw [div_le_iff₀ hyz4]
      have hkey : 16 * (‖z‖ ^ 4)⁻¹ * (‖z‖/2) ^ 4 ≤ 16 * (‖z‖ ^ 4)⁻¹ * ‖y - z‖ ^ 4 :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      have hval : 16 * (‖z‖ ^ 4)⁻¹ * (‖z‖/2) ^ 4 = 1 := by field_simp; ring
      linarith [hkey, hval ▸ hkey]
    · rw [if_neg h, if_neg h]; norm_num
  have hint : Integrable (fun z : E3 => if R < ‖z‖ then ‖V z‖ ^ 2 / ‖y - z‖ ^ 4 else 0) := by
    refine Integrable.mono' ((integrable_tailKernel hR).const_mul 16)
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact hpt z
    · by_cases h : R < ‖z‖
      · rw [if_pos h]; positivity
      · rw [if_neg h]
  calc (∫ z : E3, (if R < ‖z‖ then ‖V z‖ ^ 2 / ‖y - z‖ ^ 4 else 0))
      ≤ ∫ z : E3, 16 * tailKernel R z :=
        integral_mono hint ((integrable_tailKernel hR).const_mul 16) hpt
    _ = 48 * nsBallVol / R := by
        rw [MeasureTheory.integral_const_mul, integral_tailKernel hR]; ring

/-- The far-pressure bill vanishes as the cut radius grows. -/
theorem far_pressure_kernel_expenditure_tendsto :
    Filter.Tendsto (fun R : ℝ => 48 * nsBallVol / R) Filter.atTop (nhds 0) :=
  Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id

end ClayNS
