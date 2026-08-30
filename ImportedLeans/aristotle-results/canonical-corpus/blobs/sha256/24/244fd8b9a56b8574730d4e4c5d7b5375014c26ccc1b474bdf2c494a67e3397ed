/-
# The torus Gaussian weight `Φ_a`

The periodic analogue of the backward-heat Gaussian `exp(−|x−x₀|²/(4a))`.  On
the unit torus the Euclidean square `s²` is replaced by its `1`-periodic
analogue

  `ψ(s) = sin(πs)²/π²`,

which agrees with `s²` to second order at `s = 0` and is squeezed between
`4s²/π²` and `s²` on the fundamental interval `|s| ≤ 1/2`.  The weight is

  `Φ_a(x) = exp( − Σ_j ψ(x_j − x₀_j) / (4a) )`,          `a = ν τ`.

It is smooth, strictly positive, `ℤ³`-periodic, bounded by `1`, and equals `1`
exactly at the defect point `x₀`.  This file records those facts together with
the pointwise derivative bounds

* `ClayNS.torusGauss_le_prod` — `Φ_a(x) ≤ Π_j exp(−y_j²/(π²a))` for `|y_j| ≤ ½`
  (the Gaussian majorant, which drives every cell estimate);
* `ClayNS.abs_dvec_torusGauss_le` — `|∂_iΦ_a| ≤ (|y_i|/2a)·Φ_a`;
* `ClayNS.abs_lap_torusGauss_le` — `|ΔΦ_a| ≤ Σ_i (1/2a + y_i²/4a²)·Φ_a`;
* `ClayNS.dtime_torusGauss` — `∂_tΦ_a = 0`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.SeparableWeight

open Real

noncomputable section

namespace ClayNS

/-! ## The periodic profile `ψ(s) = sin(πs)²/π²` -/

/-- The `1`-periodic replacement for `s ↦ s²`. -/
def tgProfile (s : ℝ) : ℝ := Real.sin (π * s) ^ 2 / π ^ 2

/-- Its derivative. -/
def tgProfile1 (s : ℝ) : ℝ := 2 * Real.sin (π * s) * Real.cos (π * s) / π

/-- Its second derivative. -/
def tgProfile2 (s : ℝ) : ℝ := 2 * (Real.cos (π * s) ^ 2 - Real.sin (π * s) ^ 2)

private lemma hasDerivAt_piMul (s : ℝ) : HasDerivAt (fun u : ℝ => π * u) π s := by
  simpa using (hasDerivAt_id s).const_mul π

private lemma hasDerivAt_sinPi (s : ℝ) :
    HasDerivAt (fun u : ℝ => Real.sin (π * u)) (Real.cos (π * s) * π) s :=
  (Real.hasDerivAt_sin (π * s)).comp s (hasDerivAt_piMul s)

private lemma hasDerivAt_cosPi (s : ℝ) :
    HasDerivAt (fun u : ℝ => Real.cos (π * u)) (-Real.sin (π * s) * π) s :=
  (Real.hasDerivAt_cos (π * s)).comp s (hasDerivAt_piMul s)

lemma hasDerivAt_tgProfile (s : ℝ) : HasDerivAt tgProfile (tgProfile1 s) s := by
  have hsq : HasDerivAt (fun u : ℝ => Real.sin (π * u) ^ 2)
      (2 * Real.sin (π * s) ^ 1 * (Real.cos (π * s) * π)) s := (hasDerivAt_sinPi s).pow 2
  refine (hsq.div_const (π ^ 2)).congr_deriv ?_
  rw [tgProfile1]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp

lemma hasDerivAt_tgProfile1 (s : ℝ) : HasDerivAt tgProfile1 (tgProfile2 s) s := by
  have hprod : HasDerivAt (fun u : ℝ => 2 * Real.sin (π * u) * Real.cos (π * u))
      ((2 * (Real.cos (π * s) * π)) * Real.cos (π * s)
        + (2 * Real.sin (π * s)) * (-Real.sin (π * s) * π)) s :=
    ((hasDerivAt_sinPi s).const_mul 2).mul (hasDerivAt_cosPi s)
  refine (hprod.div_const π).congr_deriv ?_
  rw [tgProfile2]
  have hpi : π ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

lemma contDiff_tgProfile : ContDiff ℝ (⊤ : ℕ∞) tgProfile := by
  unfold tgProfile
  exact ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).pow 2).div_const _

lemma continuous_tgProfile : Continuous tgProfile := contDiff_tgProfile.continuous

lemma tgProfile_nonneg (s : ℝ) : 0 ≤ tgProfile s :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

lemma tgProfile_zero : tgProfile 0 = 0 := by simp [tgProfile]

lemma tgProfile_periodic (s : ℝ) : tgProfile (s + 1) = tgProfile s := by
  have h : Real.sin (π * (s + 1)) = -Real.sin (π * s) := by
    rw [show π * (s + 1) = π * s + π by ring, Real.sin_add_pi]
  simp [tgProfile, h]

/-- **The lower Gaussian squeeze** (Jordan's inequality).  On the fundamental
interval the periodic profile dominates `4s²/π²`. -/
lemma tgProfile_lower {s : ℝ} (hs : |s| ≤ 1 / 2) : 4 * s ^ 2 / π ^ 2 ≤ tgProfile s := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hx : |π * s| ≤ π / 2 := by
    rw [abs_mul, abs_of_pos hpi]; nlinarith [abs_nonneg s]
  have hj : 2 / π * |π * s| ≤ |Real.sin (π * s)| := Real.mul_abs_le_abs_sin hx
  have hps : |π * s| = π * |s| := by rw [abs_mul, abs_of_pos hpi]
  have h2 : 2 * |s| ≤ |Real.sin (π * s)| := by
    rw [hps] at hj
    have hcalc : 2 / π * (π * |s|) = 2 * |s| := by field_simp
    linarith [hcalc ▸ hj]
  have hsq : 4 * s ^ 2 ≤ Real.sin (π * s) ^ 2 := by
    nlinarith [sq_abs s, sq_abs (Real.sin (π * s)), abs_nonneg (Real.sin (π * s)), abs_nonneg s]
  rw [tgProfile]
  gcongr

/-- `|ψ′(s)| ≤ 2|s|`, for every real `s`. -/
lemma abs_tgProfile1_le (s : ℝ) : |tgProfile1 s| ≤ 2 * |s| := by
  have hpi : (0:ℝ) < π := Real.pi_pos
  have hc : |Real.cos (π * s)| ≤ 1 := Real.abs_cos_le_one _
  have hsn : |Real.sin (π * s)| ≤ |π * s| := Real.abs_sin_le_abs
  have hps : |π * s| = π * |s| := by rw [abs_mul, abs_of_pos hpi]
  rw [hps] at hsn
  have h1 : |tgProfile1 s| = 2 * |Real.sin (π * s)| * |Real.cos (π * s)| / π := by
    rw [tgProfile1, abs_div, abs_of_pos hpi, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  rw [h1, div_le_iff₀ hpi]
  nlinarith [abs_nonneg (Real.sin (π * s)), abs_nonneg (Real.cos (π * s)), abs_nonneg s]

/-- `ψ′(s)² ≤ 4s²`. -/
lemma sq_tgProfile1_le (s : ℝ) : tgProfile1 s ^ 2 ≤ 4 * s ^ 2 := by
  nlinarith [abs_tgProfile1_le s, sq_abs (tgProfile1 s), sq_abs s,
    abs_nonneg (tgProfile1 s), abs_nonneg s]

/-- `|ψ″(s)| ≤ 2`, for every real `s`. -/
lemma abs_tgProfile2_le (s : ℝ) : |tgProfile2 s| ≤ 2 := by
  have h := Real.sin_sq_add_cos_sq (π * s)
  rw [tgProfile2, abs_le]
  constructor <;> nlinarith [sq_nonneg (Real.sin (π * s)), sq_nonneg (Real.cos (π * s))]

/-! ## The weight -/

/-- **The torus Gaussian weight** of concentration parameter `a > 0`, centred at
`x₀`:  `Φ_a(x) = exp(−Σ_j sin(π(x_j−x₀_j))²/(4aπ²))`. -/
def torusGauss (a : ℝ) (x0 : E3) : STime → ℝ := sepExp (-(1 / (4 * a))) tgProfile x0

lemma torusGauss_pos (a : ℝ) (x0 : E3) (z : STime) : 0 < torusGauss a x0 z :=
  sepExp_pos _ _ _ _

lemma torusGauss_nonneg (a : ℝ) (x0 : E3) (z : STime) : 0 ≤ torusGauss a x0 z :=
  (torusGauss_pos a x0 z).le

lemma torusGauss_le_one {a : ℝ} (ha : 0 < a) (x0 : E3) (z : STime) :
    torusGauss a x0 z ≤ 1 :=
  sepExp_le_one (neg_nonpos.2 (by positivity)) tgProfile_nonneg x0 z

lemma torusGauss_center (a : ℝ) (x0 : E3) (t : ℝ) : torusGauss a x0 (t, x0) = 1 :=
  sepExp_center tgProfile_zero _ x0 t

lemma contDiff_torusGauss (a : ℝ) (x0 : E3) : ContDiff ℝ (⊤ : ℕ∞) (torusGauss a x0) :=
  contDiff_sepExp contDiff_tgProfile _ x0

lemma continuous_torusGauss (a : ℝ) (x0 : E3) : Continuous (torusGauss a x0) :=
  continuous_sepExp continuous_tgProfile _ x0

lemma spacePeriodic_torusGauss (a : ℝ) (x0 : E3) : SpacePeriodic (torusGauss a x0) :=
  spacePeriodic_sepExp tgProfile_periodic _ x0

/-- **The Gaussian majorant.**  On the fundamental cell centred at `x₀` the
torus weight is dominated by a genuine Gaussian of width `π√a`. -/
lemma torusGauss_le_prod {a : ℝ} (ha : 0 < a) (x0 : E3) (z : STime)
    (h : ∀ j, |z.2 j - x0 j| ≤ 1 / 2) :
    torusGauss a x0 z ≤ ∏ j, Real.exp (-((z.2 j - x0 j) ^ 2 / (π ^ 2 * a))) := by
  have hsum : ∑ j, 4 * (z.2 j - x0 j) ^ 2 / π ^ 2 ≤ sepSum tgProfile x0 z :=
    Finset.sum_le_sum fun j _ => tgProfile_lower (h j)
  have hprod : (∏ j, Real.exp (-((z.2 j - x0 j) ^ 2 / (π ^ 2 * a))))
      = Real.exp (∑ j, -((z.2 j - x0 j) ^ 2 / (π ^ 2 * a))) := by rw [Real.exp_sum]
  have heq : ∑ j, -((z.2 j - x0 j) ^ 2 / (π ^ 2 * a))
      = -(1 / (4 * a)) * ∑ j, 4 * (z.2 j - x0 j) ^ 2 / π ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [torusGauss, sepExp, hprod]
  refine Real.exp_le_exp.2 ?_
  rw [heq]
  have hc : (0:ℝ) < 1 / (4 * a) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsum hc.le]

/-! ## Derivatives of the torus weight -/

theorem dvec_torusGauss (a : ℝ) (x0 : E3) (i : Fin 3) (z : STime) :
    dvec (0, ee i) (torusGauss a x0) z
      = -(1 / (4 * a)) * tgProfile1 (z.2 i - x0 i) * torusGauss a x0 z :=
  dvec_sepExp hasDerivAt_tgProfile _ x0 i z

theorem dtime_torusGauss (a : ℝ) (x0 : E3) (z : STime) :
    dvec (1, 0) (torusGauss a x0) z = 0 :=
  dtime_sepExp hasDerivAt_tgProfile _ x0 z

theorem lap_torusGauss (a : ℝ) (x0 : E3) (z : STime) :
    lap (torusGauss a x0) z
      = (∑ i, (-(1 / (4 * a)) * tgProfile2 (z.2 i - x0 i)
          + (-(1 / (4 * a))) ^ 2 * tgProfile1 (z.2 i - x0 i) ^ 2)) * torusGauss a x0 z :=
  lap_sepExp hasDerivAt_tgProfile hasDerivAt_tgProfile1 _ x0 z

/-- **The gradient bound.**  `|∂_iΦ_a| ≤ (|y_i|/2a)·Φ_a`. -/
theorem abs_dvec_torusGauss_le {a : ℝ} (ha : 0 < a) (x0 : E3) (i : Fin 3) (z : STime) :
    |dvec (0, ee i) (torusGauss a x0) z|
      ≤ |z.2 i - x0 i| / (2 * a) * torusGauss a x0 z := by
  rw [dvec_torusGauss a x0 i z, abs_mul, abs_mul,
    abs_of_pos (torusGauss_pos a x0 z), abs_neg,
    abs_of_pos (by positivity : (0:ℝ) < 1 / (4 * a))]
  have h4 : (0:ℝ) < 1 / (4 * a) := by positivity
  have hmul := mul_le_mul_of_nonneg_left (abs_tgProfile1_le (z.2 i - x0 i)) h4.le
  have heq : 1 / (4 * a) * (2 * |z.2 i - x0 i|) = |z.2 i - x0 i| / (2 * a) := by
    field_simp
    ring
  have hkey : 1 / (4 * a) * |tgProfile1 (z.2 i - x0 i)| ≤ |z.2 i - x0 i| / (2 * a) := by
    linarith [heq ▸ hmul]
  exact mul_le_mul_of_nonneg_right hkey (torusGauss_nonneg a x0 z)

/-- **The Laplacian bound.**  `|ΔΦ_a| ≤ Σ_i (1/2a + y_i²/4a²)·Φ_a`. -/
theorem abs_lap_torusGauss_le {a : ℝ} (ha : 0 < a) (x0 : E3) (z : STime) :
    |lap (torusGauss a x0) z|
      ≤ (∑ i, (1 / (2 * a) + (z.2 i - x0 i) ^ 2 / (4 * a ^ 2))) * torusGauss a x0 z := by
  rw [lap_torusGauss a x0 z, abs_mul, abs_of_pos (torusGauss_pos a x0 z)]
  refine mul_le_mul_of_nonneg_right ?_ (torusGauss_nonneg a x0 z)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have h4 : (0:ℝ) < 1 / (4 * a) := by positivity
  have hA : |(-(1 / (4 * a))) * tgProfile2 (z.2 i - x0 i)| ≤ 1 / (2 * a) := by
    rw [abs_mul, abs_neg, abs_of_pos h4]
    have hmul := mul_le_mul_of_nonneg_left (abs_tgProfile2_le (z.2 i - x0 i)) h4.le
    have heq : 1 / (4 * a) * 2 = 1 / (2 * a) := by field_simp; ring
    linarith [heq ▸ hmul]
  have hB : |(-(1 / (4 * a))) ^ 2 * tgProfile1 (z.2 i - x0 i) ^ 2|
      ≤ (z.2 i - x0 i) ^ 2 / (4 * a ^ 2) := by
    have habs : |(-(1 / (4 * a))) ^ 2 * tgProfile1 (z.2 i - x0 i) ^ 2|
        = 1 / (16 * a ^ 2) * tgProfile1 (z.2 i - x0 i) ^ 2 := by
      rw [abs_of_nonneg (by positivity)]
      congr 1
      field_simp
      ring
    rw [habs]
    have hmul := mul_le_mul_of_nonneg_left (sq_tgProfile1_le (z.2 i - x0 i))
      (by positivity : (0:ℝ) ≤ 1 / (16 * a ^ 2))
    have heq : 1 / (16 * a ^ 2) * (4 * (z.2 i - x0 i) ^ 2)
        = (z.2 i - x0 i) ^ 2 / (4 * a ^ 2) := by field_simp; ring
    linarith [heq ▸ hmul]
  calc |(-(1 / (4 * a))) * tgProfile2 (z.2 i - x0 i)
          + (-(1 / (4 * a))) ^ 2 * tgProfile1 (z.2 i - x0 i) ^ 2|
      ≤ |(-(1 / (4 * a))) * tgProfile2 (z.2 i - x0 i)|
        + |(-(1 / (4 * a))) ^ 2 * tgProfile1 (z.2 i - x0 i) ^ 2| := abs_add_le _ _
    _ ≤ 1 / (2 * a) + (z.2 i - x0 i) ^ 2 / (4 * a ^ 2) := add_le_add hA hB

end ClayNS
