import Synthesis.RiemannQuantitativeCanonicalTaper
import Synthesis.RiemannGammaCenteredConeExact
import Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair

/-!
# Normalized canonical centered reflection-pair kernel

The remaining H2 problem lives at ordinate gaps |delta| comparable with |t|.
For the explicit canonical taper the natural variables are therefore

  v     = t u,
  q     = delta / t,
  alpha = a / t.

At the selected sample radius r=t/16, the centered modulation becomes exactly

  cos(r u)-1 = cos(v/16)-1,

while

  cosh(a u) = cosh(alpha v),
  cos(delta u) = cos(q v).

This file records that exact normalization on the literal reflection-pair
kernel before any absolute-value or curvature estimate is taken.

The normalized taper is deliberately defined by pullback from the actual
canonical taper, so there is no same-object gap:

  G_t(v) = g_t(v/t).

The next shell theorem can therefore work directly with the fixed normalized
support and frequency q=delta/t instead of paying the t-growing C^2 curvature
of g_t in the original u-coordinate.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair

def normalizedCanonicalTaper (t v : ℝ) : ℝ :=
  quantitativeCanonicalTaper t (v / t)

def normalizedCenteredCanonicalTaper (t v : ℝ) : ℝ :=
  normalizedCanonicalTaper t v * (Real.cos (v / 16) - 1)

def normalizedCenteredPairKernel
    (t a delta v : ℝ) : ℝ :=
  4 * normalizedCenteredCanonicalTaper t v
    * Real.cosh ((a / t) * v)
    * Real.cos ((delta / t) * v)

theorem quantitativeSampleRadius_mul_div
    {t v : ℝ} (ht : t ≠ 0) :
    quantitativeSampleRadius t * (v / t) = v / 16 := by
  unfold quantitativeSampleRadius
  field_simp [ht]
  ring

theorem centeredCanonicalTaper_normalized
    {t v : ℝ} (ht : t ≠ 0) :
    gammaCenteredTaper
        (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t)
        (v / t)
      =
    normalizedCenteredCanonicalTaper t v := by
  unfold gammaCenteredTaper normalizedCenteredCanonicalTaper
    normalizedCanonicalTaper
  rw [quantitativeSampleRadius_mul_div ht]

theorem normalized_cosh_argument
    {t a v : ℝ} (ht : t ≠ 0) :
    a * (v / t) = (a / t) * v := by
  field_simp [ht]
  ring

theorem normalized_cos_argument
    {t delta v : ℝ} (ht : t ≠ 0) :
    delta * (v / t) = (delta / t) * v := by
  field_simp [ht]
  ring

/--
Exact pointwise normalized form of the literal centered reflection-pair kernel.
No estimate and no absolute value is used.
-/
theorem reflectionPairWeight_centeredCanonical_normalized
    {t a delta v : ℝ} (ht : t ≠ 0) :
    reflectionPairWeight
        (gammaCenteredTaper
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t))
        a delta (v / t)
      =
    normalizedCenteredPairKernel t a delta v := by
  unfold reflectionPairWeight normalizedCenteredPairKernel
  rw [centeredCanonicalTaper_normalized ht,
      normalized_cosh_argument ht,
      normalized_cos_argument ht]

/--
The ordinate shell variable becomes a dimensionless normalized frequency.
-/
theorem normalized_gap_frequency
    {t delta q : ℝ} (ht : t ≠ 0)
    (hq : delta = q * t) :
    delta / t = q := by
  rw [hq]
  field_simp [ht]

theorem normalizedPairKernel_of_gap_eq_q_mul_t
    {t a delta q v : ℝ} (ht : t ≠ 0)
    (hq : delta = q * t) :
    normalizedCenteredPairKernel t a delta v
      =
    4 * normalizedCenteredCanonicalTaper t v
      * Real.cosh ((a / t) * v)
      * Real.cos (q * v) := by
  unfold normalizedCenteredPairKernel
  rw [normalized_gap_frequency ht hq]

/--
The canonical support window |u| < 9*pi/(4*t) becomes the t-independent
normalized window |v| < 9*pi/4.
-/
theorem canonical_support_normalizes
    {t u : ℝ} (ht : 0 < t)
    (hu : |u| < 9 * Real.pi / (4 * t)) :
    |t * u| < 9 * Real.pi / 4 := by
  have habs : |t * u| = t * |u| := by
    rw [abs_mul, abs_of_pos ht]
  rw [habs]
  have hm := mul_lt_mul_of_pos_left hu ht
  field_simp [ne_of_gt ht] at hm
  exact hm

/--
Conversely, normalized support |v|<9*pi/4 pulls back to the canonical
u-support at u=v/t.
-/
theorem normalized_support_pulls_back
    {t v : ℝ} (ht : 0 < t)
    (hv : |v| < 9 * Real.pi / 4) :
    |v / t| < 9 * Real.pi / (4 * t) := by
  rw [abs_div, abs_of_pos ht]
  exact (div_lt_div_iff_of_pos_right ht).2 (by
    have h : |v| < 9 * Real.pi / 4 := hv
    simpa [div_eq_mul_inv] using h)

/--
Exact integral normalization of the literal centered reflection-pair response.

This is the key H2 coordinate change: all t-dependence from support shrinkage is
moved into the explicit Jacobian 1/t, the dimensionless horizontal parameter
a/t, the normalized frequency delta/t, and the (bounded) canonical mixing
coefficient inside normalizedCanonicalTaper.
-/
theorem integral_reflectionPairWeight_centeredCanonical_normalized
    {t a delta : ℝ} (ht : 0 < t) :
    (∫ u : ℝ,
      reflectionPairWeight
        (gammaCenteredTaper
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t))
        a delta u)
      =
    (1 / t) *
      ∫ v : ℝ, normalizedCenteredPairKernel t a delta v := by
  let F : ℝ → ℝ := fun v => normalizedCenteredPairKernel t a delta v
  have hpoint :
      (fun u : ℝ =>
        reflectionPairWeight
          (gammaCenteredTaper
            (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t))
          a delta u)
        =
      fun u : ℝ => F (t * u) := by
    funext u
    dsimp [F]
    have htne : t ≠ 0 := ne_of_gt ht
    have htu : (t * u) / t = u := by
      field_simp [htne]
    rw [← htu]
    exact reflectionPairWeight_centeredCanonical_normalized htne
  rw [hpoint]
  have hscale :=
    Measure.integral_comp_mul_left F t
  have habs : |t⁻¹| = 1 / t := by
    rw [abs_of_pos (inv_pos.mpr ht)]
    rfl
  simpa [habs, smul_eq_mul] using hscale

/--
If the gap is written delta=q*t, the normalized integral has literal Fourier
frequency q on the fixed v-support.
-/
theorem integral_reflectionPairWeight_centeredCanonical_gap_q
    {t a delta q : ℝ} (ht : 0 < t)
    (hq : delta = q * t) :
    (∫ u : ℝ,
      reflectionPairWeight
        (gammaCenteredTaper
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t))
        a delta u)
      =
    (1 / t) *
      ∫ v : ℝ,
        4 * normalizedCenteredCanonicalTaper t v
          * Real.cosh ((a / t) * v)
          * Real.cos (q * v) := by
  rw [integral_reflectionPairWeight_centeredCanonical_normalized ht]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v =>
    normalizedPairKernel_of_gap_eq_q_mul_t (ne_of_gt ht) hq


end Synthesis
