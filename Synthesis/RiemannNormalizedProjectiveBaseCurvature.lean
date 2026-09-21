import Synthesis.RiemannProjectiveMonotoneWeightCovariance
import Synthesis.RiemannNormalizedProjectiveBaseTransformDerivative

/-!
# Positive curvature of the canonical projective base kernel at the deleted fibre

The q-only projective base transform is

  Phi_t(q) = integral P_t(v) cos(q v) dv,

with Phi_t(0)=0.  The second moment of the physical profile has a strict sign.

After v=t*u and r=t/16,

  integral P_t(v) v^2 dv
    = 4 t^3 integral g_t(u) u^2 B_r(u) du,

where B_r is the two-radius projective bracket.  The weight u^2 is strictly
increasing in |u|, so the monotone-weight covariance theorem makes the final
integral strictly negative.  Consequently

  Phi_t''(0) = - integral P_t(v) v^2 dv > 0.

This is genuine analytic information, not an explicit-formula rearrangement.
It also rules out the simplest hoped-for pointwise sign route: the canonical
q-only test cannot be nonpositive in a punctured neighbourhood of q=0.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilProjectiveResidualDecomposition
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

def normalizedProjectiveProfileSignedSecondMoment (t : ℝ) : ℝ :=
  ∫ v : ℝ, normalizedProjectivePhysicalProfile t v * v^2

theorem canonical_u_sq_projective_covariance_neg
    {t : ℝ} (ht : 18 ≤ t) :
    (∫ u : ℝ,
      quantitativeCanonicalTaper t u * u^2 *
        twoRadiusBracket
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t) u) < 0 := by
  let hd := quantitativeCanonicalGateData ht
  obtain ⟨u0, v0, hu0, hv0, huv⟩ := hd.twoPoint
  apply integral_weight_mul_twoRadiusBracket_neg
    hd.smooth.continuous hd.compactSupport hd.nonneg
    (by fun_prop : Continuous (fun u : ℝ => u^2))
    hd.radiusPos hd.radial
  · intro u v hu hv huvle
    have hs : u^2 ≤ v^2 := by
      rw [← sq_abs u, ← sq_abs v]
      exact sq_le_sq₀ (abs_nonneg u) huvle
    exact hs
  · exact hu0
  · exact hv0
  · exact huv
  · intro huvlt
    rw [← sq_abs u0, ← sq_abs v0]
    exact sq_lt_sq₀ (abs_nonneg u0) huvlt
  · intro hvult
    rw [← sq_abs v0, ← sq_abs u0]
    exact sq_lt_sq₀ (abs_nonneg v0) hvult

theorem normalizedProjectiveProfileSignedSecondMoment_scaled
    {t : ℝ} (ht : 18 ≤ t) :
    normalizedProjectiveProfileSignedSecondMoment t
      =
    4 * t^3 *
      (∫ u : ℝ,
        quantitativeCanonicalTaper t u * u^2 *
          twoRadiusBracket
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t) u) := by
  have htpos : 0 < t := by linarith
  have ht0 : t ≠ 0 := ne_of_gt htpos
  let F : ℝ → ℝ := fun v =>
    normalizedProjectivePhysicalProfile t v * v^2
  have hpoint :
      (fun u : ℝ => F (t*u))
        =
      fun u : ℝ =>
        4 * t^2 *
          (quantitativeCanonicalTaper t u * u^2 *
            twoRadiusBracket
              (quantitativeCanonicalTaper t)
              (quantitativeSampleRadius t) u) := by
    funext u
    dsimp [F]
    unfold normalizedProjectivePhysicalProfile
    have hfixed :
        normalizedCanonicalFixedProfile t (t*u)
          = quantitativeCanonicalTaper t u := by
      have htu : (t*u)/t = u := by field_simp [ht0]
      rw [← htu]
      exact (normalizedCanonicalTaper_eq_fixedProfile htpos).symm
    rw [hfixed]
    unfold twoRadiusBracket
    unfold quantitativeSampleRadius
    field_simp [ht0]
    ring
  have hscale := Measure.integral_comp_mul_left F t
  have habs : |t⁻¹| = 1 / t := by
    rw [abs_of_pos (inv_pos.mpr htpos)]
    rfl
  have hscaled :
      (∫ u : ℝ, F (t*u))
        = (1/t) * ∫ v : ℝ, F v := by
    simpa [habs, smul_eq_mul] using hscale
  rw [hpoint, integral_const_mul] at hscaled
  unfold normalizedProjectiveProfileSignedSecondMoment
  field_simp [ht0] at hscaled ⊢
  nlinarith

theorem normalizedProjectiveProfileSignedSecondMoment_neg
    {t : ℝ} (ht : 18 ≤ t) :
    normalizedProjectiveProfileSignedSecondMoment t < 0 := by
  rw [normalizedProjectiveProfileSignedSecondMoment_scaled ht]
  have hcov := canonical_u_sq_projective_covariance_neg ht
  have htpos : 0 < t := by linarith
  have hfac : 0 < 4 * t^3 := by positivity
  exact mul_neg_of_pos_of_neg hfac hcov

def normalizedProjectiveBaseTransformSecondDeriv (t q : ℝ) : ℝ :=
  ∫ v : ℝ,
    - normalizedProjectivePhysicalProfile t v * Real.cos (q*v) * v^2

theorem normalizedProjectiveBaseTransformDeriv_hasDerivAt
    (t q : ℝ) :
    HasDerivAt
      (normalizedProjectiveBaseTransformDeriv t)
      (normalizedProjectiveBaseTransformSecondDeriv t q)
      q := by
  let F : ℝ → ℝ → ℝ := fun x v =>
    - normalizedProjectivePhysicalProfile t v * Real.sin (x*v) * v
  let F' : ℝ → ℝ → ℝ := fun x v =>
    - normalizedProjectivePhysicalProfile t v * Real.cos (x*v) * v^2
  let bound : ℝ → ℝ := fun v =>
    |normalizedProjectivePhysicalProfile t v| * |v|^2
  have hFmeas :
      ∀ᶠ x in 𝓝 q, AEStronglyMeasurable (F x) volume := by
    filter_upwards with x
    exact (by dsimp [F]; fun_prop :
      Continuous (fun v : ℝ =>
        - normalizedProjectivePhysicalProfile t v * Real.sin (x*v) * v)
      ).aestronglyMeasurable
  have hFint : Integrable (F q) volume := by
    dsimp [F]
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      (((normalizedProjectivePhysicalProfile_compact t).neg.mul_right).mul_right)
  have hF'meas : AEStronglyMeasurable (F' q) volume := by
    exact (by dsimp [F']; fun_prop :
      Continuous (fun v : ℝ =>
        - normalizedProjectivePhysicalProfile t v * Real.cos (q*v) * v^2)
      ).aestronglyMeasurable
  have hbound : Integrable bound volume := by
    dsimp [bound]
    exact
      ((normalizedProjectivePhysicalProfile_continuous t).abs.mul
        (continuous_abs.pow 2)).integrable_of_hasCompactSupport
        ((normalizedProjectivePhysicalProfile_compact t).abs.mul_right)
  have hderiv :
      ∀ᵐ v ∂volume, ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivAt (F · v) (F' x v) x := by
    filter_upwards with v
    intro x hx
    dsimp [F, F']
    fun_prop
  have hdom :
      ∀ᵐ v ∂volume, ∀ x ∈ (Set.univ : Set ℝ),
        ‖F' x v‖ ≤ bound v := by
    filter_upwards with v
    intro x hx
    dsimp [F', bound]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg, abs_pow]
    have hc := Real.abs_cos_le_one (x*v)
    nlinarith [abs_nonneg (normalizedProjectivePhysicalProfile t v), abs_nonneg v]
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (F := F) (x₀ := q)
      (s := (Set.univ : Set ℝ)) (bound := bound)
      (by simp) hFmeas hFint hF'meas hdom hbound hderiv
  simpa [normalizedProjectiveBaseTransformDeriv,
    normalizedProjectiveBaseTransformSecondDeriv, F, F'] using h.2

theorem normalizedProjectiveBaseTransformSecondDeriv_zero
    (t : ℝ) :
    normalizedProjectiveBaseTransformSecondDeriv t 0
      = - normalizedProjectiveProfileSignedSecondMoment t := by
  unfold normalizedProjectiveBaseTransformSecondDeriv
    normalizedProjectiveProfileSignedSecondMoment
  simp only [zero_mul, Real.cos_zero, mul_one]
  rw [← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by ring

theorem normalizedProjectiveBaseTransformSecondDeriv_zero_pos
    {t : ℝ} (ht : 18 ≤ t) :
    0 < normalizedProjectiveBaseTransformSecondDeriv t 0 := by
  rw [normalizedProjectiveBaseTransformSecondDeriv_zero]
  exact neg_pos.mpr (normalizedProjectiveProfileSignedSecondMoment_neg ht)

end Synthesis
