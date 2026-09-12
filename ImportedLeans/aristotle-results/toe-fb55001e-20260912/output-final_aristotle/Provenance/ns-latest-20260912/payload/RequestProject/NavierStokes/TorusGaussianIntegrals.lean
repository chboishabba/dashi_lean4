/-
# Cell integrals of the torus Gaussian weight

`C49` of the Gaussian tranche.  The weight `Φ_a` of `TorusGaussianWeight.lean`
factorises over the three coordinates,

  `Φ_a(x) = Π_j gᵃ(x_j − x₀_j)`,   `gᵃ(u) = exp(−ψ(u)/(4a))`,

and so does every pointwise bound on its derivatives.  Combining the Fubini
factorisation of the cell integral with the `1`-periodicity of each factor and
the Gaussian majorant `gᵃ(u) ≤ exp(−u²/(π²a))` on the fundamental interval
gives the three cell estimates

* `ClayNS.cellInt_torusGauss_le` — mass `≤ (π³a)^{3/2}`;
* `ClayNS.cellInt_abs_dvec_torusGauss_le` — gradient `≤ (π³a)^{3/2}/(4a)`;
* `ClayNS.cellInt_abs_lap_torusGauss_le` — Laplacian
  `≤ 3(π³a)[(π³a)^{1/2}/(2a) + π²(2π³a)^{1/2}/(2a)]`.

All three vanish as `a ↓ 0`: the mass like `a^{3/2}`, the two derivative
budgets like `a^{1/2}`.  That is the quantitative content of the concentration
gate.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.TorusGaussianWeight
import RequestProject.NavierStokes.PeriodicIntegral
import RequestProject.NavierStokes.IncrementEnergyPeriodic

open Real MeasureTheory

noncomputable section

namespace ClayNS

/-! ## Elementary Gaussian bounds -/

/-- `u²e^{−bu²} ≤ 1/b`: the elementary sup bound behind the second-moment
estimate. -/
lemma sq_mul_exp_neg_le {b : ℝ} (hb : 0 < b) (u : ℝ) :
    u ^ 2 * Real.exp (-b * u ^ 2) ≤ 1 / b := by
  have hpos : 0 < Real.exp (b * u ^ 2) := Real.exp_pos _
  have h1 : b * u ^ 2 + 1 ≤ Real.exp (b * u ^ 2) := Real.add_one_le_exp _
  have hkey : b * u ^ 2 ≤ Real.exp (b * u ^ 2) := by linarith
  have hexp : Real.exp (-b * u ^ 2) = (Real.exp (b * u ^ 2))⁻¹ := by
    rw [show -b * u ^ 2 = -(b * u ^ 2) by ring, Real.exp_neg]
  rw [hexp]
  calc u ^ 2 * (Real.exp (b * u ^ 2))⁻¹
      = (b * u ^ 2) / (b * Real.exp (b * u ^ 2)) := by
        field_simp
    _ ≤ Real.exp (b * u ^ 2) / (b * Real.exp (b * u ^ 2)) := by
        gcongr
    _ = 1 / b := by field_simp

/-- **The master one-dimensional bound.**  A nonnegative continuous function
dominated on the fundamental interval by `C·e^{−bu²}` has interval integral at
most `C√(π/b)`. -/
lemma integral_Icc_half_le_gauss {C b : ℝ} (hC : 0 ≤ C) (hb : 0 < b) {h : ℝ → ℝ}
    (hcont : Continuous h)
    (hmaj : ∀ u, |u| ≤ 1 / 2 → h u ≤ C * Real.exp (-b * u ^ 2)) :
    ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), h u ≤ C * Real.sqrt (π / b) := by
  have hint : Integrable (fun u : ℝ => C * Real.exp (-b * u ^ 2)) :=
    (integrable_exp_neg_mul_sq hb).const_mul C
  calc ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), h u
      ≤ ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), C * Real.exp (-b * u ^ 2) := by
        refine setIntegral_mono_on (hcont.integrableOn_Icc) (hint.integrableOn)
          measurableSet_Icc fun u hu => ?_
        exact hmaj u (abs_le.2 ⟨by linarith [hu.1], hu.2⟩)
    _ ≤ ∫ u : ℝ, C * Real.exp (-b * u ^ 2) :=
        setIntegral_le_integral hint
          (Filter.Eventually.of_forall fun u => by positivity)
    _ = C * Real.sqrt (π / b) := by rw [integral_const_mul, integral_gaussian]

/-! ## Factorisation of the cell integral -/

/-- **Fubini for the cell.**  The cell integral of a product of one-dimensional
factors is the product of the one-dimensional integrals. -/
theorem cellInt_prod (f : Fin 3 → ℝ → ℝ) (b : E3) :
    cellInt (fun x : E3 => ∏ j, f j (x j - b j))
      = ∏ j, ∫ u in Set.Icc (0 : ℝ) 1, f j (u - b j) := by
  rw [cellInt, cell,
    show (Set.Icc (0 : Fin 3 → ℝ) 1) = Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1) by
      rw [Set.pi_univ_Icc]; rfl,
    MeasureTheory.volume_pi, MeasureTheory.Measure.restrict_pi_pi]
  exact integral_fintype_prod_eq_prod (fun j u => f j (u - b j))

/-- **Periodic recentring.**  For a `1`-periodic factor the integral over the
cell edge is the integral over the fundamental interval centred at the origin,
whatever the offset. -/
theorem integral_Icc01_periodic_shift {f : ℝ → ℝ} (hper : Function.Periodic f 1) (b : ℝ) :
    ∫ u in Set.Icc (0 : ℝ) 1, f (u - b) = ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), f u := by
  have h1 : ∫ u in Set.Icc (0 : ℝ) 1, f (u - b) = ∫ u in (0 : ℝ)..1, f (u - b) := by
    rw [intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]
  have h2 : ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), f u
      = ∫ u in (-(1 / 2) : ℝ)..(-(1 / 2) + 1), f u := by
    rw [show (-(1 / 2) : ℝ) + 1 = 1 / 2 by ring, intervalIntegral.integral_of_le (by norm_num),
      integral_Icc_eq_integral_Ioc]
  rw [h1, h2, intervalIntegral.integral_comp_sub_right (fun x => f x) b,
    show (0 : ℝ) - b = -b by ring, show (1 : ℝ) - b = -b + 1 by ring]
  exact hper.intervalIntegral_add_eq (-b) (-(1 / 2))

/-! ## The one-dimensional factors of the torus Gaussian -/

/-- The one-dimensional factor of the torus Gaussian. -/
def tgFac (a : ℝ) (u : ℝ) : ℝ := Real.exp (-(1 / (4 * a)) * tgProfile u)

/-- The one-dimensional factor carrying the gradient. -/
def tgGrd (a : ℝ) (u : ℝ) : ℝ := 1 / (4 * a) * |tgProfile1 u| * tgFac a u

/-- The one-dimensional factor carrying the second-derivative part of the
Laplacian. -/
def tgLapA (a : ℝ) (u : ℝ) : ℝ := 1 / (4 * a) * |tgProfile2 u| * tgFac a u

/-- The one-dimensional factor carrying the squared-first-derivative part of the
Laplacian. -/
def tgLapB (a : ℝ) (u : ℝ) : ℝ := 1 / (16 * a ^ 2) * tgProfile1 u ^ 2 * tgFac a u

lemma tgFac_pos (a u : ℝ) : 0 < tgFac a u := Real.exp_pos _

lemma tgFac_nonneg (a u : ℝ) : 0 ≤ tgFac a u := (tgFac_pos a u).le

lemma continuous_tgProfile1 : Continuous tgProfile1 := by
  unfold tgProfile1; fun_prop

lemma continuous_tgProfile2 : Continuous tgProfile2 := by
  unfold tgProfile2; fun_prop

lemma tgGrd_nonneg {a : ℝ} (ha : 0 < a) (u : ℝ) : 0 ≤ tgGrd a u := by
  have h1 : (0:ℝ) ≤ 1 / (4 * a) := by positivity
  have h2 := tgFac_nonneg a u
  unfold tgGrd
  positivity

lemma tgLapA_nonneg {a : ℝ} (ha : 0 < a) (u : ℝ) : 0 ≤ tgLapA a u := by
  have h1 : (0:ℝ) ≤ 1 / (4 * a) := by positivity
  have h3 := tgFac_nonneg a u
  unfold tgLapA
  positivity

lemma tgLapB_nonneg {a : ℝ} (ha : 0 < a) (u : ℝ) : 0 ≤ tgLapB a u := by
  have h2 : (0:ℝ) ≤ 1 / (16 * a ^ 2) := by positivity
  have h3 := tgFac_nonneg a u
  unfold tgLapB
  positivity

lemma continuous_tgFac (a : ℝ) : Continuous (tgFac a) :=
  Real.continuous_exp.comp (continuous_const.mul continuous_tgProfile)

lemma continuous_tgGrd (a : ℝ) : Continuous (tgGrd a) :=
  (continuous_const.mul continuous_tgProfile1.abs).mul (continuous_tgFac a)

lemma continuous_tgLapA (a : ℝ) : Continuous (tgLapA a) :=
  (continuous_const.mul continuous_tgProfile2.abs).mul (continuous_tgFac a)

lemma continuous_tgLapB (a : ℝ) : Continuous (tgLapB a) :=
  (continuous_const.mul (continuous_tgProfile1.pow 2)).mul (continuous_tgFac a)

lemma tgFac_periodic (a : ℝ) : Function.Periodic (tgFac a) 1 := by
  intro u; simp [tgFac, tgProfile_periodic]

lemma tgProfile1_periodic (s : ℝ) : tgProfile1 (s + 1) = tgProfile1 s := by
  have hs : Real.sin (π * (s + 1)) = -Real.sin (π * s) := by
    rw [show π * (s + 1) = π * s + π by ring, Real.sin_add_pi]
  have hc : Real.cos (π * (s + 1)) = -Real.cos (π * s) := by
    rw [show π * (s + 1) = π * s + π by ring, Real.cos_add_pi]
  rw [tgProfile1, tgProfile1, hs, hc]; ring

lemma tgProfile2_periodic (s : ℝ) : tgProfile2 (s + 1) = tgProfile2 s := by
  have hs : Real.sin (π * (s + 1)) = -Real.sin (π * s) := by
    rw [show π * (s + 1) = π * s + π by ring, Real.sin_add_pi]
  have hc : Real.cos (π * (s + 1)) = -Real.cos (π * s) := by
    rw [show π * (s + 1) = π * s + π by ring, Real.cos_add_pi]
  rw [tgProfile2, tgProfile2, hs, hc]; ring

lemma tgGrd_periodic (a : ℝ) : Function.Periodic (tgGrd a) 1 := by
  intro u; simp only [tgGrd, tgProfile1_periodic, tgFac_periodic a u]

lemma tgLapA_periodic (a : ℝ) : Function.Periodic (tgLapA a) 1 := by
  intro u; simp only [tgLapA, tgProfile2_periodic, tgFac_periodic a u]

lemma tgLapB_periodic (a : ℝ) : Function.Periodic (tgLapB a) 1 := by
  intro u; simp only [tgLapB, tgProfile1_periodic, tgFac_periodic a u]

/-! ## The one-dimensional Gaussian majorants -/

lemma tgFac_le_gauss {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : |u| ≤ 1 / 2) :
    tgFac a u ≤ Real.exp (-(1 / (π ^ 2 * a)) * u ^ 2) := by
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hrw : -(1 / (π ^ 2 * a)) * u ^ 2 = -(1 / (4 * a)) * (4 * u ^ 2 / π ^ 2) := by
    field_simp
  rw [tgFac, hrw]
  refine Real.exp_le_exp.2 ?_
  have hc : (0:ℝ) < 1 / (4 * a) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left (tgProfile_lower hu) hc.le]

lemma tgGrd_le_gauss {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : |u| ≤ 1 / 2) :
    tgGrd a u ≤ 1 / (4 * a) * Real.exp (-(1 / (π ^ 2 * a)) * u ^ 2) := by
  have h1 : |tgProfile1 u| ≤ 1 := by
    have := abs_tgProfile1_le u; linarith
  have h2 := tgFac_le_gauss ha hu
  have h3 : 0 < tgFac a u := tgFac_pos a u
  have hc : (0:ℝ) < 1 / (4 * a) := by positivity
  have hmul : |tgProfile1 u| * tgFac a u ≤ 1 * Real.exp (-(1 / (π ^ 2 * a)) * u ^ 2) :=
    mul_le_mul h1 h2 h3.le zero_le_one
  calc tgGrd a u = 1 / (4 * a) * (|tgProfile1 u| * tgFac a u) := by rw [tgGrd]; ring
    _ ≤ 1 / (4 * a) * (1 * Real.exp (-(1 / (π ^ 2 * a)) * u ^ 2)) :=
        mul_le_mul_of_nonneg_left hmul hc.le
    _ = 1 / (4 * a) * Real.exp (-(1 / (π ^ 2 * a)) * u ^ 2) := by ring

lemma tgLapA_le_gauss {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : |u| ≤ 1 / 2) :
    tgLapA a u ≤ 1 / (2 * a) * Real.exp (-(1 / (π ^ 2 * a)) * u ^ 2) := by
  have h1 := abs_tgProfile2_le u
  have h2 := tgFac_le_gauss ha hu
  have h3 : 0 < tgFac a u := tgFac_pos a u
  have hc : (0:ℝ) < 1 / (4 * a) := by positivity
  have hmul : |tgProfile2 u| * tgFac a u ≤ 2 * Real.exp (-(1 / (π ^ 2 * a)) * u ^ 2) :=
    mul_le_mul h1 h2 h3.le (by norm_num)
  calc tgLapA a u = 1 / (4 * a) * (|tgProfile2 u| * tgFac a u) := by rw [tgLapA]; ring
    _ ≤ 1 / (4 * a) * (2 * Real.exp (-(1 / (π ^ 2 * a)) * u ^ 2)) :=
        mul_le_mul_of_nonneg_left hmul hc.le
    _ = 1 / (2 * a) * Real.exp (-(1 / (π ^ 2 * a)) * u ^ 2) := by
        field_simp; ring

lemma tgLapB_le_gauss {a : ℝ} (ha : 0 < a) {u : ℝ} (hu : |u| ≤ 1 / 2) :
    tgLapB a u ≤ π ^ 2 / (2 * a) * Real.exp (-(1 / (2 * π ^ 2 * a)) * u ^ 2) := by
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hsup : u ^ 2 * Real.exp (-(1 / (2 * π ^ 2 * a)) * u ^ 2) ≤ 2 * π ^ 2 * a := by
    have h := sq_mul_exp_neg_le (b := 1 / (2 * π ^ 2 * a)) (by positivity) u
    rwa [one_div_one_div] at h
  have hsplit : Real.exp (-(1 / (π ^ 2 * a)) * u ^ 2)
      = Real.exp (-(1 / (2 * π ^ 2 * a)) * u ^ 2) * Real.exp (-(1 / (2 * π ^ 2 * a)) * u ^ 2) := by
    rw [← Real.exp_add]; congr 1; field_simp; ring
  have hE : (0:ℝ) < Real.exp (-(1 / (2 * π ^ 2 * a)) * u ^ 2) := Real.exp_pos _
  calc tgLapB a u = 1 / (16 * a ^ 2) * tgProfile1 u ^ 2 * tgFac a u := rfl
    _ ≤ 1 / (16 * a ^ 2) * (4 * u ^ 2) * Real.exp (-(1 / (π ^ 2 * a)) * u ^ 2) := by
        have hcoef : (0:ℝ) ≤ 1 / (16 * a ^ 2) := by positivity
        have hmul : tgProfile1 u ^ 2 * tgFac a u
            ≤ (4 * u ^ 2) * Real.exp (-(1 / (π ^ 2 * a)) * u ^ 2) :=
          mul_le_mul (sq_tgProfile1_le u) (tgFac_le_gauss ha hu) (tgFac_nonneg a u)
            (by positivity)
        calc 1 / (16 * a ^ 2) * tgProfile1 u ^ 2 * tgFac a u
            = 1 / (16 * a ^ 2) * (tgProfile1 u ^ 2 * tgFac a u) := by ring
          _ ≤ 1 / (16 * a ^ 2) * ((4 * u ^ 2) * Real.exp (-(1 / (π ^ 2 * a)) * u ^ 2)) :=
              mul_le_mul_of_nonneg_left hmul hcoef
          _ = 1 / (16 * a ^ 2) * (4 * u ^ 2) * Real.exp (-(1 / (π ^ 2 * a)) * u ^ 2) := by
              ring
    _ = 1 / (4 * a ^ 2) * (u ^ 2 * Real.exp (-(1 / (2 * π ^ 2 * a)) * u ^ 2))
          * Real.exp (-(1 / (2 * π ^ 2 * a)) * u ^ 2) := by rw [hsplit]; ring
    _ ≤ 1 / (4 * a ^ 2) * (2 * π ^ 2 * a) * Real.exp (-(1 / (2 * π ^ 2 * a)) * u ^ 2) := by
        have hcoef : (0:ℝ) ≤ 1 / (4 * a ^ 2) := by positivity
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsup hcoef) hE.le
    _ = π ^ 2 / (2 * a) * Real.exp (-(1 / (2 * π ^ 2 * a)) * u ^ 2) := by
        field_simp; ring

/-! ## The one-dimensional integral budgets -/

/-- The one-dimensional Gaussian scale `√(π³a)`. -/
def tgY (a : ℝ) : ℝ := Real.sqrt (π ^ 3 * a)

/-- The one-dimensional Gaussian scale at half concentration, `√(2π³a)`. -/
def tgY2 (a : ℝ) : ℝ := Real.sqrt (2 * π ^ 3 * a)

lemma tgY_nonneg (a : ℝ) : 0 ≤ tgY a := Real.sqrt_nonneg _

lemma tgY2_nonneg (a : ℝ) : 0 ≤ tgY2 a := Real.sqrt_nonneg _

private lemma sqrt_gauss1 {a : ℝ} (ha : 0 < a) :
    Real.sqrt (π / (1 / (π ^ 2 * a))) = tgY a := by
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [tgY]; congr 1; field_simp

private lemma sqrt_gauss2 {a : ℝ} (ha : 0 < a) :
    Real.sqrt (π / (1 / (2 * π ^ 2 * a))) = tgY2 a := by
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  rw [tgY2]; congr 1; field_simp

lemma integral_tgFac_le {a : ℝ} (ha : 0 < a) :
    ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), tgFac a u ≤ tgY a := by
  have h := integral_Icc_half_le_gauss (C := 1) (b := 1 / (π ^ 2 * a)) zero_le_one
    (by positivity) (continuous_tgFac a) (fun u hu => by simpa using tgFac_le_gauss ha hu)
  rw [one_mul, sqrt_gauss1 ha] at h
  exact h

lemma integral_tgGrd_le {a : ℝ} (ha : 0 < a) :
    ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), tgGrd a u ≤ 1 / (4 * a) * tgY a := by
  have h := integral_Icc_half_le_gauss (C := 1 / (4 * a)) (b := 1 / (π ^ 2 * a))
    (by positivity) (by positivity) (continuous_tgGrd a) (fun u hu => tgGrd_le_gauss ha hu)
  rwa [sqrt_gauss1 ha] at h

lemma integral_tgLapA_le {a : ℝ} (ha : 0 < a) :
    ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), tgLapA a u ≤ 1 / (2 * a) * tgY a := by
  have h := integral_Icc_half_le_gauss (C := 1 / (2 * a)) (b := 1 / (π ^ 2 * a))
    (by positivity) (by positivity) (continuous_tgLapA a) (fun u hu => tgLapA_le_gauss ha hu)
  rwa [sqrt_gauss1 ha] at h

lemma integral_tgLapB_le {a : ℝ} (ha : 0 < a) :
    ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), tgLapB a u ≤ π ^ 2 / (2 * a) * tgY2 a := by
  have h := integral_Icc_half_le_gauss (C := π ^ 2 / (2 * a)) (b := 1 / (2 * π ^ 2 * a))
    (by positivity) (by positivity) (continuous_tgLapB a) (fun u hu => tgLapB_le_gauss ha hu)
  rwa [sqrt_gauss2 ha] at h

/-- The combined Laplacian factor budget. -/
lemma integral_tgLapAB_le {a : ℝ} (ha : 0 < a) :
    ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), (tgLapA a u + tgLapB a u)
      ≤ 1 / (2 * a) * tgY a + π ^ 2 / (2 * a) * tgY2 a := by
  rw [integral_add (continuous_tgLapA a).integrableOn_Icc (continuous_tgLapB a).integrableOn_Icc]
  exact add_le_add (integral_tgLapA_le ha) (integral_tgLapB_le ha)

/-! ## The product form of the weight -/

/-- **The torus Gaussian factorises.**  `Φ_a(x) = Π_j gᵃ(x_j − x₀_j)`. -/
theorem torusGauss_eq_prod (a : ℝ) (x0 : E3) (z : STime) :
    torusGauss a x0 z = ∏ j, tgFac a (z.2 j - x0 j) := by
  have hprod : (∏ j, tgFac a (z.2 j - x0 j))
      = Real.exp (∑ j, -(1 / (4 * a)) * tgProfile (z.2 j - x0 j)) := by
    rw [Real.exp_sum]; rfl
  rw [hprod, torusGauss, sepExp, sepSum, Finset.mul_sum]

/-- Continuity of a coordinate-separable product on the cell. -/
lemma continuous_cellProd {f : Fin 3 → ℝ → ℝ} (hf : ∀ j, Continuous (f j)) (b : E3) :
    Continuous (fun x : E3 => ∏ j, f j (x j - b j)) :=
  continuous_finset_prod _ fun j _ =>
    (hf j).comp (by fun_prop : Continuous fun x : E3 => x j - b j)

/-- **The separable cell budget.**  A product of nonnegative `1`-periodic
factors has cell integral at most the product of the one-dimensional budgets. -/
theorem cellInt_prod_le {f : Fin 3 → ℝ → ℝ} {C : Fin 3 → ℝ} (b : E3)
    (hnn : ∀ j u, 0 ≤ f j u) (hper : ∀ j, Function.Periodic (f j) 1)
    (hle : ∀ j, (∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), f j u) ≤ C j) :
    cellInt (fun x : E3 => ∏ j, f j (x j - b j)) ≤ ∏ j, C j := by
  rw [cellInt_prod]
  have hcongr : (∏ j, ∫ u in Set.Icc (0 : ℝ) 1, f j (u - b j))
      = ∏ j, ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), f j u :=
    Finset.prod_congr rfl fun j _ => integral_Icc01_periodic_shift (hper j) (b j)
  rw [hcongr]
  exact Finset.prod_le_prod
    (fun j _ => setIntegral_nonneg measurableSet_Icc fun u _ => hnn j u) fun j _ => hle j

/-! ## `C49`: the three cell budgets -/

/-- **The mass budget.**  `∫_cell Φ_a ≤ (π³a)^{3/2}`: the weight concentrates
like `a^{3/2}` while its value at the defect point stays `1`. -/
theorem cellInt_torusGauss_le {a : ℝ} (ha : 0 < a) (x0 : E3) (t : ℝ) :
    cellInt (fun x => torusGauss a x0 (t, x)) ≤ tgY a ^ 3 := by
  have hcong : cellInt (fun x : E3 => torusGauss a x0 (t, x))
      = cellInt (fun x : E3 => ∏ j, tgFac a (x j - x0 j)) :=
    cellInt_congr fun x => torusGauss_eq_prod a x0 (t, x)
  rw [hcong]
  have h := cellInt_prod_le (f := fun _ => tgFac a) (C := fun _ => tgY a) x0
    (fun _ u => tgFac_nonneg a u) (fun _ => tgFac_periodic a) fun _ => integral_tgFac_le ha
  simpa [Fin.prod_univ_three, pow_succ] using h

/-- The gradient of the torus Gaussian in separable product form. -/
theorem abs_dvec_torusGauss_eq_prod {a : ℝ} (ha : 0 < a) (x0 : E3) (i : Fin 3) (z : STime) :
    |dvec (0, ee i) (torusGauss a x0) z|
      = ∏ j, (if j = i then tgGrd a (z.2 j - x0 j) else tgFac a (z.2 j - x0 j)) := by
  have hpos : (0:ℝ) < ∏ j, tgFac a (z.2 j - x0 j) := Finset.prod_pos fun j _ => tgFac_pos a _
  rw [dvec_torusGauss, torusGauss_eq_prod, abs_mul, abs_of_pos hpos, abs_mul, abs_neg,
    abs_of_pos (show (0:ℝ) < 1 / (4 * a) by positivity)]
  fin_cases i <;> simp [Fin.prod_univ_three, tgGrd] <;> ring

/-! ### The sharp one-dimensional gradient budget

The crude Gaussian majorant only gives `∫ tgGrd = O(a^{-1/2})`.  The exact
answer is `O(1)`: on each half of the fundamental interval the profile
derivative has a fixed sign, so `tgGrd` is (up to sign) the derivative of the
factor `tgFac` itself, and the integral telescopes.  This is what turns the
cell gradient budget from `O(a^{1/2})` into `O(a)`. -/

/-- The one-dimensional factor is differentiable with derivative `cψ′g`. -/
lemma hasDerivAt_tgFac (a u : ℝ) :
    HasDerivAt (tgFac a) (-(1 / (4 * a)) * tgProfile1 u * tgFac a u) u := by
  have h := (Real.hasDerivAt_exp (-(1 / (4 * a)) * tgProfile u)).comp u
    ((hasDerivAt_tgProfile u).const_mul (-(1 / (4 * a))))
  have hfun : tgFac a = fun v => Real.exp (-(1 / (4 * a)) * tgProfile v) := rfl
  rw [hfun]
  convert h using 1
  ring

lemma tgProfile1_odd (u : ℝ) : tgProfile1 (-u) = - tgProfile1 u := by
  rw [tgProfile1, tgProfile1, show π * -u = -(π * u) by ring, Real.sin_neg, Real.cos_neg]
  ring

lemma tgProfile1_nonneg {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1 / 2) : 0 ≤ tgProfile1 u := by
  have hpi := Real.pi_pos
  have hs : 0 ≤ Real.sin (π * u) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith)
  have hc : 0 ≤ Real.cos (π * u) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩
  rw [tgProfile1]
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs) hc) hpi.le

lemma tgProfile1_nonpos {u : ℝ} (h0 : -(1 / 2) ≤ u) (h1 : u ≤ 0) : tgProfile1 u ≤ 0 := by
  have h := tgProfile1_nonneg (u := -u) (by linarith) (by linarith)
  rw [tgProfile1_odd] at h
  linarith

lemma integral_tgGrd_right (a : ℝ) :
    ∫ u in (0:ℝ)..(1 / 2), tgGrd a u = tgFac a 0 - tgFac a (1 / 2) := by
  have hd : ∀ u ∈ Set.uIcc (0:ℝ) (1 / 2),
      HasDerivAt (fun v => - tgFac a v) (tgGrd a u) u := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    have h1 : tgGrd a u = -(-(1 / (4 * a)) * tgProfile1 u * tgFac a u) := by
      rw [tgGrd, abs_of_nonneg (tgProfile1_nonneg hu.1 hu.2)]
      ring
    rw [h1]
    exact (hasDerivAt_tgFac a u).neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_tgGrd a).intervalIntegrable _ _)]
  ring

lemma integral_tgGrd_left (a : ℝ) :
    ∫ u in (-(1 / 2):ℝ)..0, tgGrd a u = tgFac a 0 - tgFac a (-(1 / 2)) := by
  have hd : ∀ u ∈ Set.uIcc (-(1 / 2):ℝ) 0, HasDerivAt (tgFac a) (tgGrd a u) u := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    have h1 : tgGrd a u = -(1 / (4 * a)) * tgProfile1 u * tgFac a u := by
      rw [tgGrd, abs_of_nonpos (tgProfile1_nonpos hu.1 hu.2)]
      ring
    rw [h1]
    exact hasDerivAt_tgFac a u
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_tgGrd a).intervalIntegrable _ _)]

lemma tgFac_zero (a : ℝ) : tgFac a 0 = 1 := by
  rw [tgFac, tgProfile_zero]
  simp

/-- **The sharp one-dimensional gradient budget.**  `∫ tgGrd ≤ 2`, uniformly in
`a`: the total variation of a monotone factor on each half interval is at most
its maximum value `1`. -/
theorem integral_tgGrd_le_two (a : ℝ) :
    ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), tgGrd a u ≤ 2 := by
  have hIcc : ∫ u in Set.Icc (-(1 / 2) : ℝ) (1 / 2), tgGrd a u
      = ∫ u in (-(1 / 2):ℝ)..(1 / 2), tgGrd a u := by
    rw [intervalIntegral.integral_of_le (by norm_num), integral_Icc_eq_integral_Ioc]
  rw [hIcc, ← intervalIntegral.integral_add_adjacent_intervals
      (a := -(1 / 2 : ℝ)) (b := 0) (c := 1 / 2)
      ((continuous_tgGrd a).intervalIntegrable _ _)
      ((continuous_tgGrd a).intervalIntegrable _ _),
    integral_tgGrd_left a, integral_tgGrd_right a, tgFac_zero]
  have h1 := tgFac_pos a (-(1 / 2))
  have h2 := tgFac_pos a (1 / 2)
  linarith

/-- **The gradient budget.**  `∫_cell |∂_iΦ_a| ≤ 2π³a = O(a)`: the drift part of
the adjoint residual has a full positive scaling dimension in `a = ντ`. -/
theorem cellInt_abs_dvec_torusGauss_le {a : ℝ} (ha : 0 < a) (x0 : E3) (i : Fin 3) (t : ℝ) :
    cellInt (fun x => |dvec (0, ee i) (torusGauss a x0) (t, x)|)
      ≤ 2 * tgY a ^ 2 := by
  have hcong : cellInt (fun x : E3 => |dvec (0, ee i) (torusGauss a x0) (t, x)|)
      = cellInt (fun x : E3 =>
          ∏ j, (if j = i then tgGrd a (x j - x0 j) else tgFac a (x j - x0 j))) :=
    cellInt_congr fun x => abs_dvec_torusGauss_eq_prod ha x0 i (t, x)
  rw [hcong]
  have h := cellInt_prod_le (f := fun j u => if j = i then tgGrd a u else tgFac a u)
    (C := fun j => if j = i then 2 else tgY a) x0
    (fun j u => by
      dsimp only
      split <;> [exact tgGrd_nonneg ha u; exact tgFac_nonneg a u])
    (fun j => by
      by_cases hj : j = i
      · simpa [hj] using tgGrd_periodic a
      · simpa [hj] using tgFac_periodic a)
    (fun j => by
      by_cases hj : j = i
      · simpa [hj] using integral_tgGrd_le_two a
      · simpa [hj] using integral_tgFac_le ha)
  refine h.trans (le_of_eq ?_)
  fin_cases i <;> simp [Fin.prod_univ_three] <;> ring

/-- The Laplacian of the torus Gaussian, dominated by separable products. -/
theorem abs_lap_torusGauss_le_prod {a : ℝ} (ha : 0 < a) (x0 : E3) (z : STime) :
    |lap (torusGauss a x0) z|
      ≤ ∑ i, ∏ j, (if j = i then tgLapA a (z.2 j - x0 j) + tgLapB a (z.2 j - x0 j)
                    else tgFac a (z.2 j - x0 j)) := by
  have hterm : ∀ i : Fin 3,
      (∏ j, (if j = i then tgLapA a (z.2 j - x0 j) + tgLapB a (z.2 j - x0 j)
              else tgFac a (z.2 j - x0 j)))
        = (1 / (4 * a) * |tgProfile2 (z.2 i - x0 i)|
            + 1 / (16 * a ^ 2) * tgProfile1 (z.2 i - x0 i) ^ 2) * torusGauss a x0 z := by
    intro i
    rw [torusGauss_eq_prod]
    fin_cases i <;> simp [Fin.prod_univ_three, tgLapA, tgLapB] <;> ring
  simp only [hterm]
  rw [← Finset.sum_mul, lap_torusGauss, abs_mul, abs_of_pos (torusGauss_pos a x0 z)]
  refine mul_le_mul_of_nonneg_right ?_ (torusGauss_nonneg a x0 z)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hA : |(-(1 / (4 * a))) * tgProfile2 (z.2 i - x0 i)|
      = 1 / (4 * a) * |tgProfile2 (z.2 i - x0 i)| := by
    rw [abs_mul, abs_neg, abs_of_pos (show (0:ℝ) < 1 / (4 * a) by positivity)]
  have hB : |(-(1 / (4 * a))) ^ 2 * tgProfile1 (z.2 i - x0 i) ^ 2|
      = 1 / (16 * a ^ 2) * tgProfile1 (z.2 i - x0 i) ^ 2 := by
    rw [abs_of_nonneg (by positivity)]
    congr 1
    field_simp
    ring
  calc |(-(1 / (4 * a))) * tgProfile2 (z.2 i - x0 i)
          + (-(1 / (4 * a))) ^ 2 * tgProfile1 (z.2 i - x0 i) ^ 2|
      ≤ |(-(1 / (4 * a))) * tgProfile2 (z.2 i - x0 i)|
        + |(-(1 / (4 * a))) ^ 2 * tgProfile1 (z.2 i - x0 i) ^ 2| := abs_add_le _ _
    _ = 1 / (4 * a) * |tgProfile2 (z.2 i - x0 i)|
        + 1 / (16 * a ^ 2) * tgProfile1 (z.2 i - x0 i) ^ 2 := by rw [hA, hB]

/-- **The Laplacian budget.**  `∫_cell |ΔΦ_a| = O(a^{1/2})`. -/
theorem cellInt_abs_lap_torusGauss_le {a : ℝ} (ha : 0 < a) (x0 : E3) (t : ℝ) :
    cellInt (fun x => |lap (torusGauss a x0) (t, x)|)
      ≤ 3 * ((1 / (2 * a) * tgY a + π ^ 2 / (2 * a) * tgY2 a) * tgY a ^ 2) := by
  set g : Fin 3 → E3 → ℝ := fun i x =>
    ∏ j, (if j = i then tgLapA a (x j - x0 j) + tgLapB a (x j - x0 j)
          else tgFac a (x j - x0 j)) with hg
  have hgcont : ∀ i, Continuous (g i) := fun i =>
    continuous_cellProd (f := fun j u => if j = i then tgLapA a u + tgLapB a u else tgFac a u)
      (fun j => by
        by_cases hj : j = i
        · simpa [hj] using (continuous_tgLapA a).add (continuous_tgLapB a)
        · simpa [hj] using continuous_tgFac a) x0
  have hgle : ∀ i, cellInt (g i)
      ≤ (1 / (2 * a) * tgY a + π ^ 2 / (2 * a) * tgY2 a) * tgY a ^ 2 := by
    intro i
    have h := cellInt_prod_le
      (f := fun j u => if j = i then tgLapA a u + tgLapB a u else tgFac a u)
      (C := fun j => if j = i then 1 / (2 * a) * tgY a + π ^ 2 / (2 * a) * tgY2 a else tgY a) x0
      (fun j u => by
        dsimp only
        split
        · exact add_nonneg (tgLapA_nonneg ha u) (tgLapB_nonneg ha u)
        · exact tgFac_nonneg a u)
      (fun j => by
        by_cases hj : j = i
        · simpa [hj] using (tgLapA_periodic a).add (tgLapB_periodic a)
        · simpa [hj] using tgFac_periodic a)
      (fun j => by
        by_cases hj : j = i
        · simpa [hj] using integral_tgLapAB_le ha
        · simpa [hj] using integral_tgFac_le ha)
    refine h.trans (le_of_eq ?_)
    fin_cases i <;> simp [Fin.prod_univ_three] <;> ring
  have hmono : cellInt (fun x => |lap (torusGauss a x0) (t, x)|)
      ≤ cellInt (fun x => ∑ i, g i x) := by
    refine cellInt_mono ((continuous_slice (contDiff_lapFun (contDiff_torusGauss a x0)) t).abs)
      (continuous_finset_sum _ fun i _ => hgcont i) fun x => ?_
    exact abs_lap_torusGauss_le_prod ha x0 (t, x)
  have hsum : cellInt (fun x => ∑ i, g i x) = cellInt (g 0) + cellInt (g 1) + cellInt (g 2) := by
    have h3 : ∀ x : E3, (∑ i, g i x) = g 0 x + g 1 x + g 2 x := fun x => by
      simp [Fin.sum_univ_three]
    rw [cellInt_congr h3,
      cellInt_add (f := fun x => g 0 x + g 1 x) (g := g 2) ((hgcont 0).add (hgcont 1))
        (hgcont 2),
      cellInt_add (f := g 0) (g := g 1) (hgcont 0) (hgcont 1)]
  rw [hsum] at hmono
  have := add_le_add (add_le_add (hgle 0) (hgle 1)) (hgle 2)
  linarith

end ClayNS
