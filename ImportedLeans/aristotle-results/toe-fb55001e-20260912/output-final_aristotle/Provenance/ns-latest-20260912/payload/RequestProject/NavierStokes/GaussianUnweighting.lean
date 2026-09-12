/-
# Unweighting the Gaussian budget on the concentration ball

The weight-aware budget of `GaussianWeightedAbsorption.lean` controls
*Gaussian-weighted* quantities.  The parabolic embedding
`ClayNS.parabolic_gain_of_caccioppoli` consumes *unweighted* ones.  Bridging the
two requires a lower bound for the weight on the region where the estimate is
used, and the size of that bound is exactly where the scale-invariant choice
`a = κR²` earns its keep.

The torus profile obeys `ψ(s) = sin(πs)²/π² ≤ s²`, so

  `Φ_a(x) = exp(−ψ-sum/(4a)) ≥ exp(−|x−x₀|²/(4a))`,

and on the ball of radius `ρ` about the centre this is `exp(−ρ²/(4a))`.  At a
fixed physical radius with `a → 0` that constant degenerates — which is the
correct reason not to take that limit.  With the scale-invariant choice
`a = κR²` and `ρ = R` it is the **dimensionless** constant `exp(−1/(4κ))`,
independent of `R`.

* `ClayNS.tgProfile_le_sq` — `ψ(s) ≤ s²`;
* `ClayNS.torusGauss_ge_exp_of_sq_le` — the concentration lower bound
  `Φ_a ≥ exp(−ρ²/(4a))` on `∑_j(x_j−x₀_j)² ≤ ρ²`;
* `ClayNS.torusGauss_ge_scaleInvariant` — its scale-invariant instance
  `Φ_{κR²} ≥ exp(−1/(4κ))` on the ball of radius `R`;
* `ClayNS.setIntegral_le_gaussianWeighted` — the unweighting transfer
  `∫_S f ≤ exp(ρ²/(4a))·∫_S Φ_a f` for nonnegative `f` on such a set;
* `ClayNS.setIntegral_le_gaussianWeighted_scaleInvariant` — the same with the
  `R`-independent constant `exp(1/(4κ))`.

No `sorry`, no postulates.
-/
import RequestProject.NavierStokes.ScaleInvariantWeightChoice

open Real MeasureTheory

noncomputable section

namespace ClayNS

/-! ## The profile is dominated by the Euclidean square -/

/-- `ψ(s) = sin(πs)²/π² ≤ s²`: the torus profile is dominated by the Euclidean
one, so the torus Gaussian dominates the Euclidean Gaussian. -/
lemma tgProfile_le_sq (s : ℝ) : tgProfile s ≤ s ^ 2 := by
  have hsin : |Real.sin (π * s)| ≤ |π * s| := Real.abs_sin_le_abs
  have hsq : Real.sin (π * s) ^ 2 ≤ (π * s) ^ 2 := by
    have hm := mul_self_le_mul_self (abs_nonneg (Real.sin (π * s))) hsin
    rw [← sq_abs (Real.sin (π * s)), ← sq_abs (π * s), sq, sq]
    exact hm
  have hpi : (0:ℝ) < π ^ 2 := by positivity
  rw [tgProfile, div_le_iff₀ hpi]
  nlinarith [hsq]

/-- The `ψ`-sum is dominated by the squared Euclidean distance to the centre. -/
lemma sepSum_tgProfile_le (x0 : E3) (z : STime) :
    sepSum tgProfile x0 z ≤ ∑ j, (z.2 j - x0 j) ^ 2 :=
  Finset.sum_le_sum fun _ _ => tgProfile_le_sq _

/-! ## The concentration lower bound -/

/-- **The concentration lower bound.**  On the set where the squared distance to
the centre is at most `ρ²`, the torus Gaussian is at least `exp(−ρ²/(4a))`. -/
theorem torusGauss_ge_exp_of_sq_le {a rho : ℝ} (ha : 0 < a) (x0 : E3) {z : STime}
    (hz : ∑ j, (z.2 j - x0 j) ^ 2 ≤ rho ^ 2) :
    Real.exp (-(rho ^ 2 / (4 * a))) ≤ torusGauss a x0 z := by
  have h4a : (0:ℝ) < 4 * a := by positivity
  have hsum : sepSum tgProfile x0 z ≤ rho ^ 2 :=
    le_trans (sepSum_tgProfile_le x0 z) hz
  have hmono : -(rho ^ 2 / (4 * a)) ≤ -(1 / (4 * a)) * sepSum tgProfile x0 z := by
    have hkey : 1 / (4 * a) * sepSum tgProfile x0 z ≤ 1 / (4 * a) * rho ^ 2 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    have hrw : rho ^ 2 / (4 * a) = 1 / (4 * a) * rho ^ 2 := by
      field_simp
    rw [hrw, neg_mul]
    linarith [hkey]
  exact Real.exp_le_exp.2 hmono

/-- **The scale-invariant concentration lower bound.**  With `a = κR²` the
Gaussian width is `√κ·R`, and on the ball of radius `R` about the centre the
weight is bounded below by the *dimensionless* constant `exp(−1/(4κ))`,
independent of `R`. -/
theorem torusGauss_ge_scaleInvariant {kap R : ℝ} (hkap : 0 < kap) (hR : 0 < R) (x0 : E3)
    {z : STime} (hz : ∑ j, (z.2 j - x0 j) ^ 2 ≤ R ^ 2) :
    Real.exp (-(1 / (4 * kap))) ≤ torusGauss (kap * R ^ 2) x0 z := by
  have ha : 0 < kap * R ^ 2 := by positivity
  have h := torusGauss_ge_exp_of_sq_le (a := kap * R ^ 2) (rho := R) ha x0 hz
  have heq : R ^ 2 / (4 * (kap * R ^ 2)) = 1 / (4 * kap) := by
    field_simp
  rwa [heq] at h

/-! ## Unweighting a set integral -/

/-- **The unweighting transfer.**  A nonnegative integrand on a region contained
in the concentration ball is controlled by its Gaussian-weighted integral, at
the price of the factor `exp(ρ²/(4a))`. -/
theorem setIntegral_le_gaussianWeighted {a rho : ℝ} (ha : 0 < a) (x0 : E3) (t : ℝ)
    {S : Set E3} (hS : MeasurableSet S) {f : E3 → ℝ}
    (hf0 : ∀ x ∈ S, 0 ≤ f x)
    (hball : ∀ x ∈ S, ∑ j, (x j - x0 j) ^ 2 ≤ rho ^ 2)
    (hint : IntegrableOn f S volume)
    (hintw : IntegrableOn (fun x => torusGauss a x0 (t, x) * f x) S volume) :
    (∫ x in S, f x) ≤ Real.exp (rho ^ 2 / (4 * a))
      * ∫ x in S, torusGauss a x0 (t, x) * f x := by
  have hc : (0:ℝ) < Real.exp (rho ^ 2 / (4 * a)) := Real.exp_pos _
  have hstep : (∫ x in S, f x)
      ≤ ∫ x in S, Real.exp (rho ^ 2 / (4 * a)) * (torusGauss a x0 (t, x) * f x) := by
    refine MeasureTheory.setIntegral_mono_on hint (hintw.const_mul _) hS ?_
    intro x hx
    have hlow : Real.exp (-(rho ^ 2 / (4 * a))) ≤ torusGauss a x0 (t, x) :=
      torusGauss_ge_exp_of_sq_le ha x0 (z := (t, x)) (hball x hx)
    have hmul := mul_le_mul_of_nonneg_right hlow (hf0 x hx)
    have hexp : Real.exp (rho ^ 2 / (4 * a)) * Real.exp (-(rho ^ 2 / (4 * a))) = 1 := by
      rw [← Real.exp_add]; simp
    calc f x = Real.exp (rho ^ 2 / (4 * a))
          * (Real.exp (-(rho ^ 2 / (4 * a))) * f x) := by rw [← mul_assoc, hexp, one_mul]
      _ ≤ Real.exp (rho ^ 2 / (4 * a)) * (torusGauss a x0 (t, x) * f x) :=
        mul_le_mul_of_nonneg_left hmul hc.le
  rwa [MeasureTheory.integral_const_mul] at hstep

/-- **The unweighting transfer at the scale-invariant weight.**  On the ball of
radius `R` with `a = κR²`, the unweighting constant is `exp(1/(4κ))`: it does
not depend on `R`, so the transfer is uniform across scales. -/
theorem setIntegral_le_gaussianWeighted_scaleInvariant {kap R : ℝ} (hkap : 0 < kap)
    (hR : 0 < R) (x0 : E3) (t : ℝ) {S : Set E3} (hS : MeasurableSet S) {f : E3 → ℝ}
    (hf0 : ∀ x ∈ S, 0 ≤ f x)
    (hball : ∀ x ∈ S, ∑ j, (x j - x0 j) ^ 2 ≤ R ^ 2)
    (hint : IntegrableOn f S volume)
    (hintw : IntegrableOn (fun x => torusGauss (kap * R ^ 2) x0 (t, x) * f x) S volume) :
    (∫ x in S, f x) ≤ Real.exp (1 / (4 * kap))
      * ∫ x in S, torusGauss (kap * R ^ 2) x0 (t, x) * f x := by
  have ha : 0 < kap * R ^ 2 := by positivity
  have h := setIntegral_le_gaussianWeighted (a := kap * R ^ 2) (rho := R) ha x0 t hS
    hf0 hball hint hintw
  have heq : R ^ 2 / (4 * (kap * R ^ 2)) = 1 / (4 * kap) := by field_simp
  rwa [heq] at h

end ClayNS
