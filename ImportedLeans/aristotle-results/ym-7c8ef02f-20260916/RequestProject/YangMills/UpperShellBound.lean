/-
# Row A — the *upper* shell Gaussian bound

Row A's completion condition is a **two-sided** cumulative statement

    b₋·(m − k) ≤ Σ_{j=k+1}^{m} β_{Z,j} ≤ b₊·(m − k),

together with a summable interaction debt.  The lower half `b₋` is the Ward
patch floor already established (`cellGaussianFloor_of_wardPatch`, and its
regularity-driven refinements).  This file supplies the missing upper half.

The whole content is that the pointwise radial majorant

    |I(q)| ≤ (c_V²/32 + 4K_W²)·‖q‖⁻²          (`abs_literalOneLoopIntegrand_le_radial`)

integrates to a *finite explicit* number in four dimensions:

    ∫_{ℝ⁴} radialCutoff‖x‖ dx = 4 · vol(B_∞(0,1)) · ∫₀¹ y dy = 4 · 16 · ½ = 32,

the sup-norm unit ball of `Fin 4 → ℝ` being the cube of volume `16`.  Hence

    |cellGaussianCoefficient I| ≤ 32·(c_V²/32 + 4K_W²) = c_V² + 128·K_W².

Main results:

* `integral_radialCutoff_norm` — the exact value `32` of the four-dimensional
  radial-cutoff integral.
* `abs_cellGaussianCoefficient_le` — the explicit upper bound on the shell
  Gaussian coefficient.
* `cellGaussian_two_sided` — the two-sided cell bound, floor and ceiling for the
  same integrand.
* `shellGaussian_cumulative_two_sided` — the cumulative prefix form
  `b₋(m − k) ≤ Σ_{j∈Ico k m} β_{Z,j} ≤ b₊(m − k)` that Row A actually asks for.

**Row A is not closed.**  This file closes only the ceiling half of the shell
Gaussian obligation; the source-identification chain and the five remainder
channel majorants remain.
-/
import RequestProject.YangMills.LiteralIntegrability

namespace YangMills

open Real Matrix Finset MeasureTheory Set

/-! ## 1. The four-dimensional radial-cutoff integral -/

/-- The polar integrand of `radialCutoff` in four dimensions is the truncated
identity `y ↦ y·1_{y ≤ 1}`. -/
theorem radialCutoff_polar_eq {y : ℝ} (hy : y ∈ Ioi (0 : ℝ)) :
    y ^ (4 - 1) • radialCutoff y = (if y ≤ 1 then y else 0) := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  simp only [radialCutoff, smul_eq_mul]
  by_cases h : y ≤ 1
  · simp only [if_pos h]; field_simp
  · simp [h]

/-- `∫₀^∞ y³·radialCutoff y dy = 1/2`. -/
theorem integral_radialCutoff_polar :
    ∫ y in Ioi (0 : ℝ), y ^ (4 - 1) • radialCutoff y = 1 / 2 := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy => radialCutoff_polar_eq hy)]
  have hi1 : IntegrableOn (fun y : ℝ => if y ≤ 1 then y else 0) (Ioc (0 : ℝ) 1) := by
    refine IntegrableOn.congr_fun (f := fun y : ℝ => y) continuous_id.integrableOn_Ioc ?_
      measurableSet_Ioc
    intro y hy; simp [hy.2]
  have hi2 : IntegrableOn (fun y : ℝ => if y ≤ 1 then y else 0) (Ioi (1 : ℝ)) := by
    refine IntegrableOn.congr_fun (f := fun _ : ℝ => (0 : ℝ)) integrableOn_zero ?_
      measurableSet_Ioi
    intro y hy; simp [not_le.mpr (mem_Ioi.mp hy)]
  have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) := by
    rw [Set.Ioc_union_Ioi_eq_Ioi (by norm_num)]
  have hdisj : Disjoint (Ioc (0 : ℝ) 1) (Ioi (1 : ℝ)) := by
    simp only [Set.disjoint_left]
    intro a ha hb; exact absurd ha.2 (not_le.mpr hb)
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioi hi1 hi2]
  have h1 : ∫ y in Ioc (0 : ℝ) 1, (if y ≤ 1 then y else 0) = ∫ y in Ioc (0 : ℝ) 1, y := by
    refine setIntegral_congr_fun measurableSet_Ioc ?_
    intro y hy; simp [hy.2]
  have h2 : ∫ y in Ioi (1 : ℝ), (if y ≤ 1 then y else 0) = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero ?_
    intro y hy; simp [not_le.mpr (mem_Ioi.mp hy)]
  rw [h1, h2, add_zero, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  simp [integral_id]

/-- The sup-norm unit ball of `Fin 4 → ℝ` is the cube `(-1,1)⁴`, of volume `16`. -/
theorem volume_unitBall_pi : volume (Metric.ball (0 : Fin 4 → ℝ) 1) = 16 := by
  rw [ball_pi' 0 1, volume_pi_pi]
  simp [Real.volume_ball]
  norm_num

/-- **The four-dimensional radial-cutoff integral equals `32`.** -/
theorem integral_radialCutoff_norm :
    ∫ x : Fin 4 → ℝ, radialCutoff ‖x‖ = 32 := by
  have hrank : Module.finrank ℝ (Fin 4 → ℝ) = 4 := by simp
  rw [MeasureTheory.integral_fun_norm_addHaar volume radialCutoff, hrank]
  have hb : (volume : Measure (Fin 4 → ℝ)).real (Metric.ball 0 1) = 16 := by
    rw [Measure.real, volume_unitBall_pi]; norm_num
  rw [hb, integral_radialCutoff_polar]
  norm_num

theorem integral_radialCutoff_norm_const_mul (C : ℝ) :
    ∫ x : Fin 4 → ℝ, C * radialCutoff ‖x‖ = 32 * C := by
  rw [MeasureTheory.integral_const_mul, integral_radialCutoff_norm]; ring

/-! ## 2. The ceiling on the shell Gaussian coefficient -/

/-- **The shell Gaussian coefficient of the literal one-loop integrand is
bounded above by an explicit constant** built from the same two data as the
integrability proof: the linear-vanishing constant `c_V` of the transverse
conjugate of the vertex and the seagull size `K_W`.

`b₊ = c_V² + 128·K_W²`. -/
theorem abs_cellGaussianCoefficient_le
    {Vm Wm : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {cV KW : ℝ}
    (hcV : 0 ≤ cV) (hKW : 0 ≤ KW)
    (hVm : ∀ a b, Measurable fun x => Vm x a b)
    (hWm : ∀ a b, Measurable fun x => Wm x a b)
    (hsym : ∀ x, (Vm x)ᵀ = Vm x)
    (hconj : ∀ x ∈ puncturedCell, ∀ a b,
      |(transverseProjector (phatVec x) * Vm x * transverseProjector (phatVec x)) a b|
        ≤ cV * ‖x‖)
    (hWbd : ∀ x ∈ puncturedCell, ∀ a b, |Wm x a b| ≤ KW) :
    |cellGaussianCoefficient (literalOneLoopIntegrand Vm Wm)| ≤ cV ^ 2 + 128 * KW ^ 2 := by
  set C : ℝ := cV ^ 2 / 32 + 4 * KW ^ 2 with hC
  have hCnn : 0 ≤ C := by positivity
  have hint : IntegrableOn (literalOneLoopIntegrand Vm Wm) puncturedCell :=
    literalOneLoopIntegrand_integrableOn_of_conjBound hcV hKW hVm hWm hsym hconj hWbd
  have hgint : Integrable (fun x : Fin 4 → ℝ => C * radialCutoff ‖x‖) :=
    integrable_radialCutoff_norm.const_mul C
  have hstep : ∫ x in puncturedCell, |literalOneLoopIntegrand Vm Wm x|
      ≤ ∫ x in puncturedCell, C * radialCutoff ‖x‖ :=
    setIntegral_mono_on hint.abs hgint.integrableOn measurableSet_puncturedCell
      (fun x hx => abs_literalOneLoopIntegrand_le_radial hcV hKW hsym hconj hWbd hx)
  have hfull : ∫ x in puncturedCell, C * radialCutoff ‖x‖
      ≤ ∫ x : Fin 4 → ℝ, C * radialCutoff ‖x‖ := by
    refine setIntegral_le_integral hgint ?_
    filter_upwards with x
    exact mul_nonneg hCnn (radialCutoff_nonneg _)
  have hval : ∫ x : Fin 4 → ℝ, C * radialCutoff ‖x‖ = 32 * C :=
    integral_radialCutoff_norm_const_mul C
  have habs : |∫ x in puncturedCell, literalOneLoopIntegrand Vm Wm x|
      ≤ ∫ x in puncturedCell, |literalOneLoopIntegrand Vm Wm x| :=
    abs_integral_le_integral_abs
  have hfinal : |∫ x in puncturedCell, literalOneLoopIntegrand Vm Wm x| ≤ 32 * C := by
    calc |∫ x in puncturedCell, literalOneLoopIntegrand Vm Wm x|
        ≤ ∫ x in puncturedCell, |literalOneLoopIntegrand Vm Wm x| := habs
      _ ≤ ∫ x in puncturedCell, C * radialCutoff ‖x‖ := hstep
      _ ≤ ∫ x : Fin 4 → ℝ, C * radialCutoff ‖x‖ := hfull
      _ = 32 * C := hval
  have hcell : cellGaussianCoefficient (literalOneLoopIntegrand Vm Wm)
      = ∫ x in puncturedCell, literalOneLoopIntegrand Vm Wm x := by
    rw [cellGaussianCoefficient, setIntegral_puncturedCell]
  rw [hcell]
  have h32 : 32 * C = cV ^ 2 + 128 * KW ^ 2 := by rw [hC]; ring
  rw [h32] at hfinal
  exact hfinal

/-- **Two-sided cell bound.**  With a Ward-patch floor for the (nonnegative)
integrand and the radial majorant, the shell Gaussian coefficient is pinned
between two explicit constants. -/
theorem cellGaussian_two_sided
    {Vm Wm : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {cV KW c : ℝ}
    (hcV : 0 ≤ cV) (hKW : 0 ≤ KW)
    (hVm : ∀ a b, Measurable fun x => Vm x a b)
    (hWm : ∀ a b, Measurable fun x => Wm x a b)
    (hsym : ∀ x, (Vm x)ᵀ = Vm x)
    (hconj : ∀ x ∈ puncturedCell, ∀ a b,
      |(transverseProjector (phatVec x) * Vm x * transverseProjector (phatVec x)) a b|
        ≤ cV * ‖x‖)
    (hWbd : ∀ x ∈ puncturedCell, ∀ a b, |Wm x a b| ≤ KW)
    (hnonneg : ∀ q ∈ puncturedCell, 0 ≤ literalOneLoopIntegrand Vm Wm q)
    (hpatch : ∀ q ∈ wardPatch, c ≤ literalOneLoopIntegrand Vm Wm q) :
    1 / 256 * c ≤ cellGaussianCoefficient (literalOneLoopIntegrand Vm Wm)
      ∧ cellGaussianCoefficient (literalOneLoopIntegrand Vm Wm) ≤ cV ^ 2 + 128 * KW ^ 2 := by
  refine ⟨cellGaussianFloor_of_wardPatch
    (literalOneLoopIntegrand_integrableOn_of_conjBound hcV hKW hVm hWm hsym hconj hWbd)
    hnonneg hpatch, ?_⟩
  exact le_trans (le_abs_self _)
    (abs_cellGaussianCoefficient_le hcV hKW hVm hWm hsym hconj hWbd)

/-! ## 3. Cumulative prefix sums -/

/-- **The cumulative two-sided Gaussian bound over a block of shells.**  If every
shell coefficient in `[k, m)` lies between `bm` and `bp`, then the cumulative sum
grows linearly in the number of shells with those two rates.  This is the shape
Row A requires of the running coupling. -/
theorem shellGaussian_cumulative_two_sided
    {betaZ : ℕ → ℝ} {bm bp : ℝ} {k m : ℕ}
    (hlow : ∀ j ∈ Finset.Ico k m, bm ≤ betaZ j)
    (hhigh : ∀ j ∈ Finset.Ico k m, betaZ j ≤ bp) :
    bm * (m - k : ℕ) ≤ ∑ j ∈ Finset.Ico k m, betaZ j
      ∧ ∑ j ∈ Finset.Ico k m, betaZ j ≤ bp * (m - k : ℕ) := by
  have hcard : (Finset.Ico k m).card = m - k := Nat.card_Ico k m
  constructor
  · calc bm * (m - k : ℕ) = ∑ _j ∈ Finset.Ico k m, bm := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring
      _ ≤ ∑ j ∈ Finset.Ico k m, betaZ j := Finset.sum_le_sum hlow
  · calc ∑ j ∈ Finset.Ico k m, betaZ j ≤ ∑ _j ∈ Finset.Ico k m, bp := Finset.sum_le_sum hhigh
      _ = bp * (m - k : ℕ) := by rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring

/-- **Row A's two-sided cumulative shell bound for the literal one-loop
Gaussian sector.**  Uniformly in the shell index and the admissible history, with
one linear-vanishing constant `c_V` and one seagull size `K_W`, and a Ward-patch
floor `c`, the cumulative Gaussian sector over `m − k` shells is trapped between
`(c/256)(m−k)` and `(c_V² + 128K_W²)(m−k)`. -/
theorem shellGaussianOfIntegrand_cumulative_two_sided
    {Vm Wm : ℕ → (ℕ → ℝ) → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {cV KW c : ℝ}
    (hcV : 0 ≤ cV) (hKW : 0 ≤ KW)
    (hVm : ∀ j h a b, Measurable fun x => Vm j h x a b)
    (hWm : ∀ j h a b, Measurable fun x => Wm j h x a b)
    (hsym : ∀ j h x, (Vm j h x)ᵀ = Vm j h x)
    (hconj : ∀ j h, ∀ x ∈ puncturedCell, ∀ a b,
      |(transverseProjector (phatVec x) * Vm j h x * transverseProjector (phatVec x)) a b|
        ≤ cV * ‖x‖)
    (hWbd : ∀ j h, ∀ x ∈ puncturedCell, ∀ a b, |Wm j h x a b| ≤ KW)
    (hnonneg : ∀ j h, ∀ q ∈ puncturedCell,
      0 ≤ literalOneLoopIntegrand (Vm j h) (Wm j h) q)
    (hpatch : ∀ j h, ∀ q ∈ wardPatch, c ≤ literalOneLoopIntegrand (Vm j h) (Wm j h) q)
    (h : ℕ → ℝ) (k m : ℕ) :
    (1 / 256 * c) * (m - k : ℕ)
        ≤ ∑ j ∈ Finset.Ico k m,
            shellGaussianOfIntegrand
              (fun j' h' => literalOneLoopIntegrand (Vm j' h') (Wm j' h')) j h
      ∧ ∑ j ∈ Finset.Ico k m,
            shellGaussianOfIntegrand
              (fun j' h' => literalOneLoopIntegrand (Vm j' h') (Wm j' h')) j h
          ≤ (cV ^ 2 + 128 * KW ^ 2) * (m - k : ℕ) := by
  refine shellGaussian_cumulative_two_sided (betaZ := fun j =>
    shellGaussianOfIntegrand (fun j' h' => literalOneLoopIntegrand (Vm j' h') (Wm j' h')) j h)
    (fun j _ => ?_) (fun j _ => ?_)
  · exact (cellGaussian_two_sided hcV hKW (hVm j h) (hWm j h) (hsym j h) (hconj j h)
      (hWbd j h) (hnonneg j h) (hpatch j h)).1
  · exact (cellGaussian_two_sided hcV hKW (hVm j h) (hWm j h) (hsym j h) (hconj j h)
      (hWbd j h) (hnonneg j h) (hpatch j h)).2

end YangMills
