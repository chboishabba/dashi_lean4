/-
# The tilted log-variance is a projective speed

The Gram identity behind the similarity analysis,

  `‖∂_τ V̂‖² = (AB − C²)/A²`,   `A = ⟪V,V⟫`, `B = ⟪W,W⟫`, `C = ⟪V,W⟫`,

is not specific to Navier–Stokes: it holds for any differentiable curve in an
inner product space (`ClayNS.projective_speed_sq`).  This file records the
instance in which the curve is an **exponentially tilted vector**,

  `w_α(i) = e^{α λ_i/2} a_i`,   so   `∂_α w_α(i) = (λ_i/2)·w_α(i)`,

for which, with the tilted moments `S_j(α) = Σ_i λ_i^j w_α(i)²`,

  `A = S₀`,  `C = ½S₁`,  `B = ¼S₂`,   hence   `‖∂_α ŵ_α‖² = ¼(S₀S₂ − S₁²)/S₀²`.

So a tilted log-variance is *literally* the squared speed of the normalized
vector in projective space: the same quantity the similarity analysis of the
Navier–Stokes profile pays for.

## What is proved

* `ClayNS.tiltVec`, `ClayNS.tiltMoment` — the tilted vector and its moments;
* `ClayNS.hasDerivAt_tiltVec` — `∂_α w_α(i) = (λ_i/2)w_α(i)`;
* `ClayNS.tilt_gram_A`, `ClayNS.tilt_gram_C`, `ClayNS.tilt_gram_B` — the three
  Gram coefficients in terms of `S₀`, `S₁`, `S₂`;
* `ClayNS.tilted_gram_eq_log_variance` — `(AB − C²)/A² = ¼(S₀S₂ − S₁²)/S₀²`;
* `ClayNS.tilted_projective_speed` — the same statement read as the squared
  projective speed of the normalized tilted vector, via
  `ClayNS.projective_speed_sq`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.SimilarityEnergy

open RealInnerProductSpace
open scoped BigOperators

noncomputable section

namespace ClayNS

variable {ι : Type*} [Fintype ι]

/-- The exponentially tilted vector `w_α(i) = e^{αλ_i/2}a_i`. -/
def tiltVec (lam a : ι → ℝ) (al : ℝ) (i : ι) : ℝ := Real.exp (al * lam i / 2) * a i

/-- The tilted moment `S_j(α) = Σ_i λ_i^j w_α(i)²`. -/
def tiltMoment (lam a : ι → ℝ) (j : ℕ) (al : ℝ) : ℝ :=
  ∑ i, lam i ^ j * (tiltVec lam a al i) ^ 2

omit [Fintype ι] in
/-- **`∂_α w_α = (λ/2)w_α`**: the tilt derivative is multiplication by half the
log-frequency. -/
theorem hasDerivAt_tiltVec (lam a : ι → ℝ) (al : ℝ) (i : ι) :
    HasDerivAt (fun b : ℝ => tiltVec lam a b i)
      (lam i / 2 * tiltVec lam a al i) al := by
  have hlin : HasDerivAt (fun b : ℝ => b * lam i / 2) (lam i / 2) al := by
    simpa using ((hasDerivAt_id al).mul_const (lam i)).div_const 2
  have hexp : HasDerivAt (fun b : ℝ => Real.exp (b * lam i / 2))
      (Real.exp (al * lam i / 2) * (lam i / 2)) al := by
    simpa [mul_comm] using (Real.hasDerivAt_exp (al * lam i / 2)).comp al hlin
  have := hexp.mul_const (a i)
  refine this.congr_deriv ?_
  simp [tiltVec]
  ring

/-- `A = S₀`. -/
theorem tilt_gram_A (lam a : ι → ℝ) (al : ℝ) :
    ∑ i, (tiltVec lam a al i) ^ 2 = tiltMoment lam a 0 al := by
  simp [tiltMoment]

/-- `C = ½S₁`. -/
theorem tilt_gram_C (lam a : ι → ℝ) (al : ℝ) :
    ∑ i, (tiltVec lam a al i) * (lam i / 2 * tiltVec lam a al i)
      = (1 / 2) * tiltMoment lam a 1 al := by
  rw [tiltMoment, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `B = ¼S₂`. -/
theorem tilt_gram_B (lam a : ι → ℝ) (al : ℝ) :
    ∑ i, (lam i / 2 * tiltVec lam a al i) ^ 2
      = (1 / 4) * tiltMoment lam a 2 al := by
  rw [tiltMoment, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The Gram defect of a tilted family is its log-variance.**
`(AB − C²)/A² = ¼(S₀S₂ − S₁²)/S₀²`. -/
theorem tilted_gram_eq_log_variance {A B C S0 S1 S2 : ℝ}
    (hA : A = S0) (hB : B = (1 / 4) * S2) (hC : C = (1 / 2) * S1) (h0 : S0 ≠ 0) :
    (A * B - C ^ 2) / A ^ 2 = (1 / 4) * ((S0 * S2 - S1 ^ 2) / S0 ^ 2) := by
  subst hA; subst hB; subst hC
  field_simp
  ring

/-- **The tilted log-variance is a projective speed.**  For a curve in an inner
product space whose Gram coefficients are those of an exponentially tilted
vector, the squared speed of the normalized curve is `¼(S₀S₂ − S₁²)/S₀²`. -/
theorem tilted_projective_speed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (V W : E) {S0 S1 S2 : ℝ}
    (hA : (⟪V, V⟫ : ℝ) = S0) (hB : (⟪W, W⟫ : ℝ) = (1 / 4) * S2)
    (hC : (⟪V, W⟫ : ℝ) = (1 / 2) * S1) (hpos : (0 : ℝ) < ⟪V, V⟫) :
    ‖(Real.sqrt ⟪V, V⟫)⁻¹ • W - (⟪V, W⟫ / (⟪V, V⟫ * Real.sqrt ⟪V, V⟫)) • V‖ ^ 2
      = (1 / 4) * ((S0 * S2 - S1 ^ 2) / S0 ^ 2) := by
  have h0 : S0 ≠ 0 := by
    rw [← hA]; exact ne_of_gt hpos
  rw [projective_speed_sq V W hpos]
  exact tilted_gram_eq_log_variance hA hB hC h0

end ClayNS
