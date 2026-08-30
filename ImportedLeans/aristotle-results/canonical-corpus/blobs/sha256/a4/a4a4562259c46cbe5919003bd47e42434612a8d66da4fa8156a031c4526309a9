/-
# The support-corner slack identity for the odd Taylor error polynomial

The odd finite-radius determinant chain (`OddTaylorDeterminant.lean`) controls
the determinant-level remainder by a polynomial in the *normalised* moment
coefficients

  `q_y = N 3 y / N 1 y`,      `c_y = N 5 y / (20 * N 1 y)`,

namely

  `P (q_a, q_p, c_a, c_p) = 204 (c_a + c_p) + 40 (q_a c_p + q_p c_a) + 64 c_a c_p`.

Compact support in `[0,R]` gives exactly the four coordinate bounds

  `q_a ≤ R²`, `q_p ≤ R²`, `20 c_a ≤ R⁴`, `20 c_p ≤ R⁴`,

i.e. `q ≤ U := R²` and `c ≤ C := R⁴/20`, and the support majorant

  `S R = 510 R⁴ + 100 R⁶ + 4 R⁸`

is *literally* the corner value `25 · P (U, U, C, C)`
(`supportMajorant_eq_corner_value`).

The point of this module is that no optimisation, no derivative and no
multivariate monotonicity infrastructure is needed to majorise `25 P` by `S`.
The difference telescopes into four explicitly recorded *debts to saturation*
`U - q_a`, `U - q_p`, `C - c_a`, `C - c_p`, each multiplied by a manifestly
nonnegative factor:

  `oddTaylorSupportPolynomialSlackIdentity`  (a ring identity), and
  `oddTaylorSupportPolynomialMajorization`   (its ordered consequence).

Finally, `exists_radius_supportMajorant_lt` records the *radius freedom* that
makes the whole quantitative gate cheap: a strictly positive continuum margin
`Δ > 0` is by itself enough to produce an admissible radius, because `r` is
universally quantified below a threshold everywhere downstream.  No lower bound
on the TP₂ margin is required.

No `sorry`, no `axiom`, no numerical evidence.
-/

import Mathlib

namespace RiemannAnalytic
namespace OddTaylorSupportSlack

/-! ## The two polynomials -/

/-- The normalised determinant-level error polynomial of the odd Taylor chain,
in the normalised coefficients `q_a, q_p` (cubic) and `c_a, c_p` (quintic). -/
def normalizedErrorPolynomial (qa qp ca cp : ℝ) : ℝ :=
  204 * (ca + cp) + 40 * (qa * cp + qp * ca) + 64 * (ca * cp)

/-- The compact-support majorant `S R = 510 R⁴ + 100 R⁶ + 4 R⁸`. -/
def supportMajorant (R : ℝ) : ℝ := 510 * R ^ 4 + 100 * R ^ 6 + 4 * R ^ 8

/-- The saturation corner: `U = R²` for the cubic coefficients. -/
def cornerQ (R : ℝ) : ℝ := R ^ 2

/-- The saturation corner: `C = R⁴/20` for the quintic coefficients. -/
noncomputable def cornerC (R : ℝ) : ℝ := R ^ 4 / 20

/-- **The support majorant is exactly the corner value.**  `S R` is not a loose
estimate: it is `25` times the value of the normalised error polynomial at the
support-extremal corner `(R², R², R⁴/20, R⁴/20)`. -/
theorem supportMajorant_eq_corner_value (R : ℝ) :
    supportMajorant R
      = 25 * normalizedErrorPolynomial (cornerQ R) (cornerQ R) (cornerC R) (cornerC R) := by
  simp only [supportMajorant, normalizedErrorPolynomial, cornerQ, cornerC]
  ring

/-! ## The slack identity -/

/-- **Slack identity.**  `S - 25 P` telescopes into the four debts to
saturation `U - q_a`, `U - q_p`, `C - c_a`, `C - c_p`, each carrying an
explicitly nonnegative cofactor.  This is a pure ring identity. -/
theorem oddTaylorSupportPolynomialSlackIdentity (R qa qp ca cp : ℝ) :
    supportMajorant R - 25 * normalizedErrorPolynomial qa qp ca cp
      = 25 * (40 * cornerC R * ((cornerQ R - qa) + (cornerQ R - qp))
          + (cornerC R - ca) * (204 + 40 * qp + 64 * cornerC R)
          + (cornerC R - cp) * (204 + 40 * qa + 64 * ca)) := by
  simp only [supportMajorant, normalizedErrorPolynomial, cornerQ, cornerC]
  ring

/-! ## The ordered consequence -/

/-- **Support majorization.**  Under exactly the four support bounds
`q_a ≤ R²`, `q_p ≤ R²`, `20 c_a ≤ R⁴`, `20 c_p ≤ R⁴` together with
nonnegativity of `q_a, q_p, c_a`, the normalised error polynomial satisfies

  `25 P (q_a, q_p, c_a, c_p) ≤ 510 R⁴ + 100 R⁶ + 4 R⁸`.

Only the slack identity and positivity are used — no optimisation theorem. -/
theorem oddTaylorSupportPolynomialMajorization {R qa qp ca cp : ℝ}
    (hqa : qa ≤ R ^ 2) (hqp : qp ≤ R ^ 2)
    (hca : 20 * ca ≤ R ^ 4) (hcp : 20 * cp ≤ R ^ 4)
    (hqa0 : 0 ≤ qa) (hqp0 : 0 ≤ qp) (hca0 : 0 ≤ ca) :
    25 * normalizedErrorPolynomial qa qp ca cp ≤ supportMajorant R := by
  have hC0 : 0 ≤ cornerC R := by
    simp only [cornerC]; positivity
  have hCa : 0 ≤ cornerC R - ca := by
    simp only [cornerC]; linarith
  have hCp : 0 ≤ cornerC R - cp := by
    simp only [cornerC]; linarith
  have hQa : 0 ≤ cornerQ R - qa := by
    simp only [cornerQ]; linarith
  have hQp : 0 ≤ cornerQ R - qp := by
    simp only [cornerQ]; linarith
  have t1 : 0 ≤ 40 * cornerC R * ((cornerQ R - qa) + (cornerQ R - qp)) := by
    have : 0 ≤ (cornerQ R - qa) + (cornerQ R - qp) := by linarith
    positivity
  have t2 : 0 ≤ (cornerC R - ca) * (204 + 40 * qp + 64 * cornerC R) := by
    have : 0 ≤ 204 + 40 * qp + 64 * cornerC R := by linarith
    exact mul_nonneg hCa this
  have t3 : 0 ≤ (cornerC R - cp) * (204 + 40 * qa + 64 * ca) := by
    have : 0 ≤ 204 + 40 * qa + 64 * ca := by linarith
    exact mul_nonneg hCp this
  have hid := oddTaylorSupportPolynomialSlackIdentity R qa qp ca cp
  linarith

/-! ## The quantitative radius gate -/

/-- The sufficient condition `S r² < 900 Δ` implies the gate the odd
determinant chain actually consumes, `P r² < 36 Δ`. -/
theorem oddTaylorRadiusGate {R r Δ qa qp ca cp : ℝ}
    (hqa : qa ≤ R ^ 2) (hqp : qp ≤ R ^ 2)
    (hca : 20 * ca ≤ R ^ 4) (hcp : 20 * cp ≤ R ^ 4)
    (hqa0 : 0 ≤ qa) (hqp0 : 0 ≤ qp) (hca0 : 0 ≤ ca)
    (hgate : supportMajorant R * r ^ 2 < 900 * Δ) :
    normalizedErrorPolynomial qa qp ca cp * r ^ 2 < 36 * Δ := by
  have hmaj := oddTaylorSupportPolynomialMajorization hqa hqp hca hcp hqa0 hqp0 hca0
  have hr2 : (0 : ℝ) ≤ r ^ 2 := by positivity
  have : 25 * normalizedErrorPolynomial qa qp ca cp * r ^ 2 ≤ supportMajorant R * r ^ 2 :=
    mul_le_mul_of_nonneg_right hmaj hr2
  linarith

/-- **Radius freedom (threshold form).**  A strictly positive margin `Δ` is by
itself enough: for any nonnegative support majorant `S` there is a strictly
positive threshold below which every radius satisfies `S r² < 900 Δ`.  No
quantitative lower bound on `Δ` is needed, which is exactly why the strict TP₂
inequality suffices. -/
theorem exists_threshold_supportMajorant_lt {S Δ : ℝ} (hS : 0 ≤ S) (hΔ : 0 < Δ) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → S * r ^ 2 < 900 * Δ := by
  have hS1 : (0 : ℝ) < S + 1 := by linarith
  refine ⟨min 1 (Δ / (S + 1)), lt_min one_pos (by positivity), fun r hr hlt => ?_⟩
  have hr1 : r ≤ 1 := le_of_lt (lt_of_lt_of_le hlt (min_le_left _ _))
  have hr2 : r < Δ / (S + 1) := lt_of_lt_of_le hlt (min_le_right _ _)
  have hrS : r * (S + 1) < Δ := (lt_div_iff₀ hS1).1 hr2
  have hsq : r ^ 2 ≤ r := by nlinarith
  calc S * r ^ 2 ≤ S * r := mul_le_mul_of_nonneg_left hsq hS
    _ = r * S := mul_comm _ _
    _ < Δ := by nlinarith
    _ < 900 * Δ := by linarith

/-- **Radius freedom.**  From a strictly positive margin one gets an admissible
radius outright. -/
theorem exists_radius_supportMajorant_lt {S Δ : ℝ} (hS : 0 ≤ S) (hΔ : 0 < Δ) :
    ∃ r : ℝ, 0 < r ∧ S * r ^ 2 < 900 * Δ := by
  obtain ⟨r₀, hr₀, h⟩ := exists_threshold_supportMajorant_lt hS hΔ
  exact ⟨r₀ / 2, by linarith, h _ (by linarith) (by linarith)⟩

/-- **Radius freedom, packaged for the odd gate.**  From a strictly positive
continuum margin `Δ` and compact support radius `R` one gets a strictly
positive observation radius at which the normalised error polynomial is beaten
by the margin, for *every* admissible coefficient tuple. -/
theorem exists_radius_oddTaylorRadiusGate {R Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ r : ℝ, 0 < r ∧ ∀ qa qp ca cp : ℝ,
      qa ≤ R ^ 2 → qp ≤ R ^ 2 → 20 * ca ≤ R ^ 4 → 20 * cp ≤ R ^ 4 →
      0 ≤ qa → 0 ≤ qp → 0 ≤ ca →
      normalizedErrorPolynomial qa qp ca cp * r ^ 2 < 36 * Δ := by
  have hS : 0 ≤ supportMajorant R := by
    simp only [supportMajorant]; positivity
  obtain ⟨r, hr, hlt⟩ := exists_radius_supportMajorant_lt hS hΔ
  exact ⟨r, hr, fun qa qp ca cp h1 h2 h3 h4 h5 h6 h7 =>
    oddTaylorRadiusGate h1 h2 h3 h4 h5 h6 h7 hlt⟩

end OddTaylorSupportSlack
end RiemannAnalytic
