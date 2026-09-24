import Synthesis.RiemannNormalizedCanonicalFixedProfile
import Synthesis.RiemannNormalizedCenteredOffShell

/-!
# Two-radius normalized centered canonical profiles

The projective/centered gauge bridge requires centered radius differences at
both r and 2r.  The existing normalized H2 carrier was specialized to the
canonical selected radius

  r = t/16.

This file pays the missing second-radius representation seam by parameterizing
the normalized centered profile by a scale k:

  H_{t,k}(v) = G_t(v) (cos(k v / 16) - 1).

Then
  k=1  is the existing radius r=t/16,
  k=2  is the projective companion radius 2r=t/8.

All identities are exact same-object rewrites from the literal canonical taper.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.LiteralWeilParityBalance
open Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair

def normalizedCenteredCanonicalTaperAtScale
    (t k v : ℝ) : ℝ :=
  normalizedCanonicalTaper t v * (Real.cos (k * v / 16) - 1)

def normalizedCenteredFixedProfileAtScale
    (t k v : ℝ) : ℝ :=
  normalizedCanonicalFixedProfile t v * (Real.cos (k * v / 16) - 1)

def normalizedCenteredPairKernelAtScale
    (t k a delta v : ℝ) : ℝ :=
  4 * normalizedCenteredFixedProfileAtScale t k v
    * Real.cosh ((a / t) * v)
    * Real.cos ((delta / t) * v)

theorem scaledQuantitativeSampleRadius_mul_div
    {t k v : ℝ} (ht : t ≠ 0) :
    (k * quantitativeSampleRadius t) * (v / t)
      = k * v / 16 := by
  unfold quantitativeSampleRadius
  field_simp [ht]
  ring

theorem centeredCanonicalTaperAtScale_normalized
    {t k v : ℝ} (ht : t ≠ 0) :
    gammaCenteredTaper
        (quantitativeCanonicalTaper t)
        (k * quantitativeSampleRadius t)
        (v / t)
      =
    normalizedCenteredCanonicalTaperAtScale t k v := by
  unfold gammaCenteredTaper normalizedCenteredCanonicalTaperAtScale
    normalizedCanonicalTaper
  rw [scaledQuantitativeSampleRadius_mul_div ht]

theorem normalizedCenteredCanonicalTaperAtScale_eq_fixed
    {t k v : ℝ} (ht : 0 < t) :
    normalizedCenteredCanonicalTaperAtScale t k v
      =
    normalizedCenteredFixedProfileAtScale t k v := by
  unfold normalizedCenteredCanonicalTaperAtScale
    normalizedCenteredFixedProfileAtScale
  rw [normalizedCanonicalTaper_eq_fixedProfile ht]

theorem normalizedCenteredFixedProfileAtScale_one
    (t v : ℝ) :
    normalizedCenteredFixedProfileAtScale t 1 v
      = normalizedCenteredFixedProfile t v := by
  unfold normalizedCenteredFixedProfileAtScale normalizedCenteredFixedProfile
  ring_nf
  rfl

theorem normalizedCenteredFixedProfileAtScale_two
    (t v : ℝ) :
    normalizedCenteredFixedProfileAtScale t 2 v
      =
    normalizedCanonicalFixedProfile t v
      * (Real.cos (v / 8) - 1) := by
  unfold normalizedCenteredFixedProfileAtScale
  congr 1
  congr 1
  ring

theorem reflectionPairWeight_centeredCanonicalAtScale_normalized
    {t k a delta v : ℝ} (ht : t ≠ 0) :
    reflectionPairWeight
        (gammaCenteredTaper
          (quantitativeCanonicalTaper t)
          (k * quantitativeSampleRadius t))
        a delta (v / t)
      =
    4 * normalizedCenteredCanonicalTaperAtScale t k v
      * Real.cosh ((a / t) * v)
      * Real.cos ((delta / t) * v) := by
  unfold reflectionPairWeight
  rw [centeredCanonicalTaperAtScale_normalized ht,
      normalized_cosh_argument ht,
      normalized_cos_argument ht]

theorem reflectionPairWeight_centeredCanonicalAtScale_fixed
    {t k a delta v : ℝ} (ht : 0 < t) :
    reflectionPairWeight
        (gammaCenteredTaper
          (quantitativeCanonicalTaper t)
          (k * quantitativeSampleRadius t))
        a delta (v / t)
      =
    normalizedCenteredPairKernelAtScale t k a delta v := by
  rw [reflectionPairWeight_centeredCanonicalAtScale_normalized (ne_of_gt ht)]
  unfold normalizedCenteredPairKernelAtScale
  rw [normalizedCenteredCanonicalTaperAtScale_eq_fixed ht]

/--
Exact integral normalization for either projective sampling radius (and in fact
any scalar multiple k of the canonical radius).
-/
theorem integral_reflectionPairWeight_centeredCanonicalAtScale_normalized
    {t k a delta : ℝ} (ht : 0 < t) :
    (∫ u : ℝ,
      reflectionPairWeight
        (gammaCenteredTaper
          (quantitativeCanonicalTaper t)
          (k * quantitativeSampleRadius t))
        a delta u)
      =
    (1 / t) *
      ∫ v : ℝ,
        normalizedCenteredPairKernelAtScale t k a delta v := by
  let F : ℝ → ℝ :=
    fun v => normalizedCenteredPairKernelAtScale t k a delta v
  have hpoint :
      (fun u : ℝ =>
        reflectionPairWeight
          (gammaCenteredTaper
            (quantitativeCanonicalTaper t)
            (k * quantitativeSampleRadius t))
          a delta u)
        =
      fun u : ℝ => F (t * u) := by
    funext u
    dsimp [F]
    have htne : t ≠ 0 := ne_of_gt ht
    have htu : (t * u) / t = u := by
      field_simp [htne]
    rw [← htu]
    exact reflectionPairWeight_centeredCanonicalAtScale_fixed ht
  rw [hpoint]
  have hscale :=
    Measure.integral_comp_mul_left F t
  have habs : |t⁻¹| = 1 / t := by
    rw [abs_of_pos (inv_pos.mpr ht)]
    rfl
  simpa [habs, smul_eq_mul] using hscale

/-- The missing literal second-radius centered normalized identity. -/
theorem integral_reflectionPairWeight_centeredCanonical_twoRadius_normalized
    {t a delta : ℝ} (ht : 0 < t) :
    (∫ u : ℝ,
      reflectionPairWeight
        (gammaCenteredTaper
          (quantitativeCanonicalTaper t)
          (2 * quantitativeSampleRadius t))
        a delta u)
      =
    (1 / t) *
      ∫ v : ℝ,
        4 * normalizedCanonicalFixedProfile t v
          * (Real.cos (v / 8) - 1)
          * Real.cosh ((a / t) * v)
          * Real.cos ((delta / t) * v) := by
  rw [integral_reflectionPairWeight_centeredCanonicalAtScale_normalized
    (t := t) (k := 2) (a := a) (delta := delta) ht]
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    unfold normalizedCenteredPairKernelAtScale
    rw [normalizedCenteredFixedProfileAtScale_two]
    ring

end Synthesis
