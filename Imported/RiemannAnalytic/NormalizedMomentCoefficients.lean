/-
# Positivity of the first odd moment and the normalised moment coefficients

This module closes the two remaining ingredients that turn the abstract
support-slack algebra of `OddTaylorSupportSlack.lean` into a statement about the
*actual* taper moments

  `N k y = ∫₀ᴸ uᵏ φ(u) sinh (y u) du`.

* `oddMoment_pos` : `N k y > 0` for a taper with a positive plateau on a
  subinterval `(c,d) ⊆ (0,L]` and a positive height `y`.  The proof is the
  literal one: on `(c,d)` the integrand `uᵏ φ(u) sinh(yu)` is a product of three
  strictly positive factors, so the support of the (a.e. nonnegative) integrand
  meets `(0,L]` in a set of positive measure.  No boundary subtlety at `u = 0`
  arises because the plateau is strictly inside the positive axis.

* `normalizedCubicCoeff  L φ y = N 3 y / N 1 y`  and
  `normalizedQuinticCoeff L φ y = N 5 y / (20 * N 1 y)`,

  the coefficients the odd determinant chain actually consumes, together with
  the four support bounds

  `q_y ≤ L²`,  `20 c_y ≤ L⁴`,  `0 ≤ q_y`,  `0 ≤ c_y`,

  obtained from the pointwise support domination `N (k+j) y ≤ Lʲ N k y`
  (`oddMoment_le_of_support`, an honest `integral_mono`).

* `normalizedCoefficients_support_majorization` : the resulting instance of
  `oddTaylorSupportPolynomialMajorization` for two heights.

No `sorry`, no `axiom`, no numerical evidence.
-/

import Mathlib
import RiemannAnalytic.OddTaylorDeterminant
import RiemannAnalytic.OddTaylorSupportSlack

open MeasureTheory Set

namespace RiemannAnalytic
namespace NormalizedMomentCoefficients

open StrictKernelMomentRatio OddTaylorDeterminant OddTaylorSupportSlack

variable {L Cφ y c d m : ℝ} {φ : ℝ → ℝ}

/-! ## Strict positivity of the odd moments -/

/-- **`N k y > 0` from the plateau.**  On the plateau subinterval `(c,d)` the
integrand `uᵏ φ(u) sinh(yu)` is strictly positive, and `(c,d)` has positive
measure; the integrand is nonnegative everywhere on `(0,L]`. -/
theorem oddMoment_pos (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (hy : 0 < y)
    (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) (k : ℕ) :
    0 < oddMoment L φ k y := by
  have hint := integrable_moment hφmeas hφb hL hy k
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) L)]
      fun u => u ^ k * φ u * Real.sinh (y * u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact mul_nonneg (mul_nonneg (pow_nonneg hu.1.le k) (hφ0 u hu))
      (Real.sinh_pos_iff.2 (mul_pos hy hu.1)).le
  rw [oddMoment]
  refine (setIntegral_pos_iff_support_of_nonneg_ae hnn hint).2 ?_
  have hsub : Ioo c d
      ⊆ Function.support (fun u => u ^ k * φ u * Real.sinh (y * u)) ∩ Ioc (0 : ℝ) L := by
    intro u hu
    have hu0 : 0 < u := hc.trans hu.1
    have huL : u ≤ L := le_of_lt (lt_of_lt_of_le hu.2 hdL)
    refine ⟨?_, ⟨hu0, huL⟩⟩
    have hφu : 0 < φ u := lt_of_lt_of_le hm (hplateau u hu)
    have hsu : 0 < Real.sinh (y * u) := Real.sinh_pos_iff.2 (mul_pos hy hu0)
    have : 0 < u ^ k * φ u * Real.sinh (y * u) := by positivity
    exact ne_of_gt this
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_pos.2 (by linarith)

/-! ## The normalised coefficients -/

/-- `q_y = N 3 y / N 1 y`, the normalised cubic coefficient. -/
noncomputable def normalizedCubicCoeff (L : ℝ) (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  oddMoment L φ 3 y / oddMoment L φ 1 y

/-- `c_y = N 5 y / (20 N 1 y)`, the normalised quintic remainder coefficient
(the `20` is the constant produced by the six-scaled fifth-order sine
remainder `6 |sin x − x + x³/6| ≤ |x|⁵/20`). -/
noncomputable def normalizedQuinticCoeff (L : ℝ) (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  oddMoment L φ 5 y / (20 * oddMoment L φ 1 y)

/-- `0 ≤ q_y`. -/
theorem normalizedCubicCoeff_nonneg (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u) (hy : 0 < y) :
    0 ≤ normalizedCubicCoeff L φ y :=
  div_nonneg (oddMoment_nonneg hφ0 hy 3) (oddMoment_nonneg hφ0 hy 1)

/-- `0 ≤ c_y`. -/
theorem normalizedQuinticCoeff_nonneg (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u) (hy : 0 < y) :
    0 ≤ normalizedQuinticCoeff L φ y :=
  div_nonneg (oddMoment_nonneg hφ0 hy 5) (by linarith [oddMoment_nonneg hφ0 hy 1])

/-- **Support bound for the cubic coefficient:** `q_y ≤ L²`. -/
theorem normalizedCubicCoeff_le (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (hy : 0 < y)
    (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    normalizedCubicCoeff L φ y ≤ L ^ 2 := by
  have hN1 : 0 < oddMoment L φ 1 y :=
    oddMoment_pos hφmeas hφ0 hφb hL hy hc hcd hdL hm hplateau 1
  have h := oddMoment_le_of_support hφmeas hφ0 hφb hL hy 1 2
  norm_num at h
  rw [normalizedCubicCoeff, div_le_iff₀ hN1]
  linarith

/-- **Support bound for the quintic coefficient:** `20 c_y ≤ L⁴`. -/
theorem normalizedQuinticCoeff_le (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (hy : 0 < y)
    (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    20 * normalizedQuinticCoeff L φ y ≤ L ^ 4 := by
  have hN1 : 0 < oddMoment L φ 1 y :=
    oddMoment_pos hφmeas hφ0 hφb hL hy hc hcd hdL hm hplateau 1
  have h := oddMoment_le_of_support hφmeas hφ0 hφb hL hy 1 4
  norm_num at h
  have h20 : (0 : ℝ) < 20 * oddMoment L φ 1 y := by linarith
  rw [normalizedQuinticCoeff, mul_div_assoc', div_le_iff₀ h20]
  nlinarith

/-! ## The support majorization at the actual moments -/

/-- **Support majorization at the actual taper moments.**  For an admissible
taper with a positive plateau and two positive heights `a, p`, the normalised
determinant-level error polynomial evaluated at the actual normalised moment
coefficients is majorised by the support corner value
`510 L⁴ + 100 L⁶ + 4 L⁸`. -/
theorem normalizedCoefficients_support_majorization {a p : ℝ}
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (ha : 0 < a) (hp : 0 < p)
    (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    25 * normalizedErrorPolynomial (normalizedCubicCoeff L φ a) (normalizedCubicCoeff L φ p)
        (normalizedQuinticCoeff L φ a) (normalizedQuinticCoeff L φ p)
      ≤ supportMajorant L :=
  oddTaylorSupportPolynomialMajorization
    (normalizedCubicCoeff_le hφmeas hφ0 hφb hL ha hc hcd hdL hm hplateau)
    (normalizedCubicCoeff_le hφmeas hφ0 hφb hL hp hc hcd hdL hm hplateau)
    (normalizedQuinticCoeff_le hφmeas hφ0 hφb hL ha hc hcd hdL hm hplateau)
    (normalizedQuinticCoeff_le hφmeas hφ0 hφb hL hp hc hcd hdL hm hplateau)
    (normalizedCubicCoeff_nonneg hφ0 ha) (normalizedCubicCoeff_nonneg hφ0 hp)
    (normalizedQuinticCoeff_nonneg hφ0 ha)

/-- **The normalised TP₂ margin is strictly positive.**  Dividing the continuum
strict determinant inequality by the two positive first moments gives
`q_p − q_a > 0` at the level of the normalised coefficients. -/
theorem normalizedCubicCoeff_strictMono {a p : ℝ}
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (ha : 0 < a) (hap : a < p)
    (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    normalizedCubicCoeff L φ a < normalizedCubicCoeff L φ p := by
  have hp : 0 < p := ha.trans hap
  have hNa : 0 < oddMoment L φ 1 a :=
    oddMoment_pos hφmeas hφ0 hφb hL ha hc hcd hdL hm hplateau 1
  have hNp : 0 < oddMoment L φ 1 p :=
    oddMoment_pos hφmeas hφ0 hφb hL hp hc hcd hdL hm hplateau 1
  have hdet := oddMomentDeterminant_strictPos hφmeas hφ0 hφb hL ha hap hc hcd hdL hm hplateau
  rw [normalizedCubicCoeff, normalizedCubicCoeff, div_lt_div_iff₀ hNa hNp]
  nlinarith

/-! ## The six-scaled fifth-order sine remainder -/

/-- The fifth-order sine remainder on the whole line. -/
theorem abs_sin_sub_taylor3_all (x : ℝ) :
    |Real.sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 5 / 120 := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
    exact abs_sin_sub_taylor3 h
  · have hx : 0 ≤ -x := by linarith
    have hkey := abs_sin_sub_taylor3 hx
    have e : Real.sin x - (x - x ^ 3 / 6) = -(Real.sin (-x) - (-x - (-x) ^ 3 / 6)) := by
      rw [Real.sin_neg]; ring
    rw [abs_of_nonpos h, e, abs_neg]
    exact hkey

/-- **The six-scaled remainder.**  Multiplying the fifth-order sine remainder by
the factor `6` that the six-scaled odd response carries turns the constant
`1/120` into `1/20`, which is exactly the `20` appearing in the normalised
quintic coefficient `c_y = N 5 y / (20 N 1 y)`. -/
theorem sixScaled_sine_remainder (x : ℝ) :
    6 * |Real.sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 5 / 20 := by
  have := abs_sin_sub_taylor3_all x
  linarith

/-- The six-scaled entrywise odd remainder bound: `6 |B_y(r) − T_y(r)| ≤ (r⁵/20) N 5 y`. -/
theorem oddResponse_sub_trunc_sixScaled (hφmeas : Measurable φ)
    (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (hy : 0 < y) {r : ℝ} (hr : 0 ≤ r) :
    6 * |oddResponse L φ y r - oddTrunc L φ y r| ≤ r ^ 5 / 20 * oddMoment L φ 5 y := by
  have h := oddResponse_sub_trunc_abs_le (y := y) (r := r) hφmeas hφ0 hφb hL hy hr
  linarith

/-- The remainder bound in normalised form: `(r⁵/20) N 5 y = r⁵ c_y N 1 y`. -/
theorem quinticRemainder_normalized_form {r : ℝ} (hN1 : oddMoment L φ 1 y ≠ 0) :
    r ^ 5 / 20 * oddMoment L φ 5 y
      = r ^ 5 * (normalizedQuinticCoeff L φ y * oddMoment L φ 1 y) := by
  rw [normalizedQuinticCoeff]
  field_simp

/-- The cubic moment in normalised form: `N 3 y = q_y N 1 y`. -/
theorem cubicMoment_normalized_form (hN1 : oddMoment L φ 1 y ≠ 0) :
    oddMoment L φ 3 y = normalizedCubicCoeff L φ y * oddMoment L φ 1 y := by
  rw [normalizedCubicCoeff]
  field_simp

/-! ## Radius freedom: strict TP₂ alone closes the odd finite-radius sign -/

/-- **Odd finite-radius sign from strict TP₂ alone.**  For an admissible taper
with a positive plateau and heights `0 < a < p`, there is a strictly positive
radius threshold below which

* the quantitative support gate `S(L) r² < 900 (q_p − q_a)` holds,
* the normalised error polynomial is beaten by the margin,
  `P (q_a,q_p,c_a,c_p) r² < 36 (q_p − q_a)`, and
* the actual finite-radius odd minor is strictly negative.

Because the radius is universally quantified below a threshold — and it is so
quantified everywhere downstream (`exists_radius_both_parity_minors_neg`,
`pole_quotient_transversality`, `offline_zero_parity_transversality`) — *strict*
positivity of the TP₂ margin is all that is needed.  No quantitative lower bound
on `q_p − q_a` is required anywhere in the chain. -/
theorem strictTP2_exists_radius_strict_odd_minor {a p : ℝ}
    (hφmeas : Measurable φ) (hφ0 : ∀ u ∈ Ioc (0 : ℝ) L, 0 ≤ φ u)
    (hφb : ∀ u ∈ Ioc (0 : ℝ) L, |φ u| ≤ Cφ) (hL : 0 < L) (ha : 0 < a) (hap : a < p)
    (hc : 0 < c) (hcd : c < d) (hdL : d ≤ L) (hm : 0 < m)
    (hplateau : ∀ u ∈ Ioo c d, m ≤ φ u) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      supportMajorant L * r ^ 2
          < 900 * (normalizedCubicCoeff L φ p - normalizedCubicCoeff L φ a) ∧
      normalizedErrorPolynomial (normalizedCubicCoeff L φ a) (normalizedCubicCoeff L φ p)
          (normalizedQuinticCoeff L φ a) (normalizedQuinticCoeff L φ p) * r ^ 2
          < 36 * (normalizedCubicCoeff L φ p - normalizedCubicCoeff L φ a) ∧
      oddFiniteRadiusDeterminant L φ a p r < 0 := by
  have hp : 0 < p := ha.trans hap
  have hΔ : 0 < normalizedCubicCoeff L φ p - normalizedCubicCoeff L φ a := by
    have := normalizedCubicCoeff_strictMono hφmeas hφ0 hφb hL ha hap hc hcd hdL hm hplateau
    linarith
  have hS : 0 ≤ supportMajorant L := by
    simp only [supportMajorant]; positivity
  obtain ⟨r₁, hr₁, hgate⟩ := exists_threshold_supportMajorant_lt hS hΔ
  obtain ⟨r₂, hr₂, hminor⟩ := exists_radius_oddFiniteRadiusDeterminant_neg
    hφmeas hφ0 hφb hL ha hap hc hcd hdL hm hplateau
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun r hr hlt => ?_⟩
  have h1 : r < r₁ := lt_of_lt_of_le hlt (min_le_left _ _)
  have h2 : r < r₂ := lt_of_lt_of_le hlt (min_le_right _ _)
  refine ⟨hgate r hr h1, ?_, hminor r hr h2⟩
  exact oddTaylorRadiusGate
    (normalizedCubicCoeff_le hφmeas hφ0 hφb hL ha hc hcd hdL hm hplateau)
    (normalizedCubicCoeff_le hφmeas hφ0 hφb hL hp hc hcd hdL hm hplateau)
    (normalizedQuinticCoeff_le hφmeas hφ0 hφb hL ha hc hcd hdL hm hplateau)
    (normalizedQuinticCoeff_le hφmeas hφ0 hφb hL hp hc hcd hdL hm hplateau)
    (normalizedCubicCoeff_nonneg hφ0 ha) (normalizedCubicCoeff_nonneg hφ0 hp)
    (normalizedQuinticCoeff_nonneg hφ0 ha) (hgate r hr h1)

end NormalizedMomentCoefficients
end RiemannAnalytic
