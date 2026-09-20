import Synthesis.RiemannProjectiveSyntheticHeightSign
import Synthesis.RiemannNormalizedProjectiveHorizontalOscillation
import Synthesis.RiemannNormalizedProjectiveBaseZeroAtSameOrd

/-!
# Uniform synthetic q=0 sign of the normalized horizontal projective kernel

The literal synthetic-height identity transports exactly through v=t*u.

For t>0 and arbitrary alpha,

  alpha^2 * Q_proj(t,alpha,0)
    = -4*t * heightDefect(g_t,r_t,t*alpha,0).

Hence, on canonical GateData,

  alpha != 0  ->  Q_proj(t,alpha,0) < 0.

This removes the unnecessary hypothesis that alpha must be realized by an actual
zero on the target ordinate.  Every source zero can now use the same q=0 signed
anchor before the existing q-Lipschitz and q^-2 far estimates are applied.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair
open Zeta23Bridge.LiteralWeilProjectiveTaper
open Zeta23Bridge.LiteralWeilTwoRadiusHeightDetector

/-- Pointwise normalized/literal scaling of the projective reflection-pair
kernel. -/
theorem normalizedProjectivePhysicalProfile_scaled_cosh
    {t alpha u : ℝ} (ht : 0 < t) :
    normalizedProjectivePhysicalProfile t (t*u)
      * Real.cosh (alpha * (t*u))
      =
    reflectionPairWeight
      (projTaper
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t))
      (t*alpha) 0 u := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hfixed :
      quantitativeCanonicalTaper t u
        = normalizedCanonicalFixedProfile t (t*u) := by
    have htu : (t*u)/t = u := by
      field_simp [ht0]
    rw [← htu]
    exact normalizedCanonicalTaper_eq_fixedProfile ht
  unfold normalizedProjectivePhysicalProfile
    reflectionPairWeight projTaper twoRadiusBracket
  simp only [zero_mul, Real.cos_zero, mul_one]
  rw [← hfixed]
  unfold quantitativeSampleRadius
  congr 1
  ring_nf
  congr 1 <;> ring

/-- Integral scaling to the literal projective reflection-pair kernel. -/
theorem integral_normalizedProjectivePhysicalProfile_cosh_eq_literal
    {t alpha : ℝ} (ht : 0 < t) :
    (∫ v : ℝ,
      normalizedProjectivePhysicalProfile t v
        * Real.cosh (alpha*v))
      =
    t *
      ∫ u : ℝ,
        reflectionPairWeight
          (projTaper
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t))
          (t*alpha) 0 u := by
  let F : ℝ → ℝ := fun v =>
    normalizedProjectivePhysicalProfile t v
      * Real.cosh (alpha*v)
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hpoint :
      (fun u : ℝ =>
        reflectionPairWeight
          (projTaper
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t))
          (t*alpha) 0 u)
        =
      fun u : ℝ => F (t*u) := by
    funext u
    dsimp [F]
    exact (normalizedProjectivePhysicalProfile_scaled_cosh
      (t := t) (alpha := alpha) (u := u) ht).symm
  have hscale := Measure.integral_comp_mul_left F t
  have habs : |t⁻¹| = 1/t := by
    rw [abs_of_pos (inv_pos.mpr ht)]
    rfl
  rw [hpoint]
  have hscaled :
      (∫ u : ℝ, F (t*u))
        =
      (1/t) * ∫ v : ℝ, F v := by
    simpa [habs, smul_eq_mul] using hscale
  rw [hscaled]
  field_simp [ht0]
  ring

/-- Exact normalized synthetic-height identity at q=0. -/
theorem normalizedProjectiveHorizontalQuadratic_sq_eq_neg_heightDefect
    {t alpha : ℝ} (ht : 0 < t) :
    alpha^2 * normalizedProjectiveHorizontalQuadratic t alpha 0
      =
    -4*t *
      heightDefect
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t)
        (t*alpha) 0 := by
  have hP :
      Integrable (normalizedProjectivePhysicalProfile t) :=
    normalizedProjectivePhysicalProfile_integrable t
  have hPc :
      Integrable
        (fun v : ℝ =>
          normalizedProjectivePhysicalProfile t v
            * Real.cosh (alpha*v)) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((normalizedProjectivePhysicalProfile_compact t).mul_right)
  have hQ :=
    normalizedProjectiveHorizontalQuadratic_eq_physicalCosine
      t alpha 0
  simp only [zero_mul, Real.cos_zero, mul_one] at hQ
  have hbase :=
    normalizedProjectiveBaseTransform_eq_physicalCosine t 0
  simp only [zero_mul, Real.cos_zero, mul_one] at hbase
  have hbase0 := normalizedProjectiveBaseTransform_zero ht
  have hPzero :
      (∫ v : ℝ, normalizedProjectivePhysicalProfile t v) = 0 := by
    linarith [hbase, hbase0]
  calc
    alpha^2 * normalizedProjectiveHorizontalQuadratic t alpha 0
      =
    ∫ v : ℝ,
      alpha^2 *
        (normalizedProjectivePhysicalProfile t v
          * coshMinusOneDivSq alpha v) := by
      rw [hQ, integral_const_mul]
    _ =
    ∫ v : ℝ,
      normalizedProjectivePhysicalProfile t v
        * (Real.cosh (alpha*v) - 1) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by
        rw [cosh_sub_one_eq_sq_mul_divSq]
        ring
    _ =
    (∫ v : ℝ,
      normalizedProjectivePhysicalProfile t v
        * Real.cosh (alpha*v))
      -
    ∫ v : ℝ, normalizedProjectivePhysicalProfile t v := by
      rw [← integral_sub hPc hP]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by ring
    _ =
    ∫ v : ℝ,
      normalizedProjectivePhysicalProfile t v
        * Real.cosh (alpha*v) := by
      rw [hPzero]
      ring
    _ =
    t *
      ∫ u : ℝ,
        reflectionPairWeight
          (projTaper
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t))
          (t*alpha) 0 u :=
      integral_normalizedProjectivePhysicalProfile_cosh_eq_literal ht
    _ =
    -4*t *
      heightDefect
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t)
        (t*alpha) 0 := by
      rw [reflectionPairWeight_projTaper_zero_eq_neg_four_heightDefect
        (quantitativeCanonicalTaper_contDiff (by linarith : 18 ≤ t)).continuous
        (quantitativeCanonicalTaper_compact (by linarith : 18 ≤ t))]
      ring

/--
Uniform synthetic q=0 sign: no same-ordinate zero realization hypothesis.
-/
theorem normalizedProjectiveHorizontalQuadratic_zero_neg
    {t alpha : ℝ}
    (ht : 18 ≤ t)
    (halpha : alpha ≠ 0) :
    normalizedProjectiveHorizontalQuadratic t alpha 0 < 0 := by
  have ht0 : 0 < t := by linarith
  have hta : t*alpha ≠ 0 := mul_ne_zero (ne_of_gt ht0) halpha
  let hd := quantitativeCanonicalGateData ht
  obtain ⟨u0, v0, hu0, hv0, huv⟩ := hd.twoPoint
  have hD :
      0 <
      heightDefect
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t)
        (t*alpha) 0 := by
    exact twoRadiusEvenProfileDetectsHeight
      hd.smooth.continuous
      hd.compactSupport
      hd.nonneg
      hd.radiusPos
      hd.radial
      hu0 hv0 huv hta
  have hid :=
    normalizedProjectiveHorizontalQuadratic_sq_eq_neg_heightDefect
      (t := t) (alpha := alpha) ht0
  have ha2 : 0 < alpha^2 := sq_pos_of_ne_zero halpha
  nlinarith

end Synthesis
