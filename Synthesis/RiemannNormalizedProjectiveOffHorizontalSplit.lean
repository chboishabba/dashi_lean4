import Synthesis.RiemannNormalizedProjectiveOffTsumAttachment
import Synthesis.RiemannNormalizedCenteredOffHorizontalSplit

/-!
# Exact horizontal split of the normalized projective Off atom

The projective atom is a literal linear combination of three normalized
reflection-pair atoms: centered scale 2, centered scale 1, and radius zero.
This file performs the horizontal split on that exact combination.

The result is one q-only projective base transform plus one horizontal-strip
correction:

  A_rho^proj
    = m_rho * Phi_proj(q_rho)
      + m_rho * E_proj(alpha_rho,q_rho).

This is the correct one-dimensional Stieltjes/RvM surface for the same
projective observable consumed by the signed reflection-pair cutset.
-/

noncomputable section

open MeasureTheory Complex
open scoped Real

namespace Synthesis

open Zeta23
open Zeta23Bridge.LiteralWeilParityBalance

def normalizedCenteredBaseTransformAtScale
    (t k q : ℝ) : ℝ :=
  ∫ v : ℝ,
    4 * normalizedCenteredFixedProfileAtScale t k v
      * Real.cos (q * v)

def normalizedCenteredHorizontalCorrectionAtScale
    (t k alpha q : ℝ) : ℝ :=
  ∫ v : ℝ,
    4 * normalizedCenteredFixedProfileAtScale t k v
      * (Real.cosh (alpha * v) - 1)
      * Real.cos (q * v)

def normalizedRadiusZeroBaseTransform
    (t q : ℝ) : ℝ :=
  ∫ v : ℝ,
    4 * normalizedCanonicalFixedProfile t v
      * Real.cos (q * v)

def normalizedRadiusZeroHorizontalCorrection
    (t alpha q : ℝ) : ℝ :=
  ∫ v : ℝ,
    4 * normalizedCanonicalFixedProfile t v
      * (Real.cosh (alpha * v) - 1)
      * Real.cos (q * v)

theorem normalizedCenteredPairIntegralAtScale_eq_base_add_horizontal
    (t k alpha q : ℝ) :
    (∫ v : ℝ,
      4 * normalizedCenteredFixedProfileAtScale t k v
        * Real.cosh (alpha * v)
        * Real.cos (q * v))
      =
    normalizedCenteredBaseTransformAtScale t k q
      + normalizedCenteredHorizontalCorrectionAtScale t k alpha q := by
  unfold normalizedCenteredBaseTransformAtScale
    normalizedCenteredHorizontalCorrectionAtScale
  have hbase : Integrable
      (fun v : ℝ =>
        4 * normalizedCenteredFixedProfileAtScale t k v
          * Real.cos (q * v)) := by
    have hc : Continuous
        (fun v : ℝ =>
          4 * normalizedCenteredFixedProfileAtScale t k v
            * Real.cos (q * v)) := by
      unfold normalizedCenteredFixedProfileAtScale
      fun_prop
    have hs : HasCompactSupport
        (fun v : ℝ =>
          4 * normalizedCenteredFixedProfileAtScale t k v
            * Real.cos (q * v)) := by
      unfold normalizedCenteredFixedProfileAtScale
      exact ((normalizedCanonicalFixedProfile_compact t).mul_right.mul_left).mul_right
    exact hc.integrable_of_hasCompactSupport hs
  have hcorr : Integrable
      (fun v : ℝ =>
        4 * normalizedCenteredFixedProfileAtScale t k v
          * (Real.cosh (alpha * v) - 1)
          * Real.cos (q * v)) := by
    have hc : Continuous
        (fun v : ℝ =>
          4 * normalizedCenteredFixedProfileAtScale t k v
            * (Real.cosh (alpha * v) - 1)
            * Real.cos (q * v)) := by
      unfold normalizedCenteredFixedProfileAtScale
      fun_prop
    have hs : HasCompactSupport
        (fun v : ℝ =>
          4 * normalizedCenteredFixedProfileAtScale t k v
            * (Real.cosh (alpha * v) - 1)
            * Real.cos (q * v)) := by
      unfold normalizedCenteredFixedProfileAtScale
      exact (((normalizedCanonicalFixedProfile_compact t).mul_right.mul_left).mul_right).mul_right
    exact hc.integrable_of_hasCompactSupport hs
  rw [← integral_add hbase hcorr]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by ring

theorem normalizedRadiusZeroPairIntegral_eq_base_add_horizontal
    (t alpha q : ℝ) :
    (∫ v : ℝ,
      4 * normalizedCanonicalFixedProfile t v
        * Real.cosh (alpha * v)
        * Real.cos (q * v))
      =
    normalizedRadiusZeroBaseTransform t q
      + normalizedRadiusZeroHorizontalCorrection t alpha q := by
  unfold normalizedRadiusZeroBaseTransform
    normalizedRadiusZeroHorizontalCorrection
  have hbase : Integrable
      (fun v : ℝ =>
        4 * normalizedCanonicalFixedProfile t v
          * Real.cos (q * v)) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((normalizedCanonicalFixedProfile_compact t).mul_left.mul_right)
  have hcorr : Integrable
      (fun v : ℝ =>
        4 * normalizedCanonicalFixedProfile t v
          * (Real.cosh (alpha * v) - 1)
          * Real.cos (q * v)) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      (((normalizedCanonicalFixedProfile_compact t).mul_left.mul_right).mul_right)
  rw [← integral_add hbase hcorr]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by ring

theorem normalizedCenteredZeroAtomAtScale_eq_base_add_horizontal
    (t k : ℝ) (rho : Zeros) :
    normalizedCenteredZeroAtomAtScale t k rho
      =
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * normalizedCenteredBaseTransformAtScale
          t k (normalizedGap t rho)
      +
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * normalizedCenteredHorizontalCorrectionAtScale
          t k (normalizedHorizontalHeight t rho) (normalizedGap t rho) := by
  unfold normalizedCenteredZeroAtomAtScale
    normalizedGap normalizedHorizontalHeight
    normalizedCenteredPairKernelAtScale
  rw [normalizedCenteredPairIntegralAtScale_eq_base_add_horizontal]
  ring

theorem normalizedRadiusZeroZeroAtom_eq_base_add_horizontal
    (t : ℝ) (rho : Zeros) :
    normalizedRadiusZeroZeroAtom t rho
      =
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * normalizedRadiusZeroBaseTransform t (normalizedGap t rho)
      +
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * normalizedRadiusZeroHorizontalCorrection t
          (normalizedHorizontalHeight t rho) (normalizedGap t rho) := by
  unfold normalizedRadiusZeroZeroAtom
    normalizedGap normalizedHorizontalHeight
  rw [normalizedRadiusZeroPairIntegral_eq_base_add_horizontal]
  ring

def normalizedProjectiveBaseTransform
    (t q : ℝ) : ℝ :=
  normalizedCenteredBaseTransformAtScale t 2 q
      * onLineRadiusProfile (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t)
    - normalizedCenteredBaseTransformAtScale t 1 q
      * onLineRadiusProfile (quantitativeCanonicalTaper t)
          (2 * quantitativeSampleRadius t)
    + normalizedRadiusZeroBaseTransform t q
      * (onLineRadiusProfile (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t)
          - onLineRadiusProfile (quantitativeCanonicalTaper t)
            (2 * quantitativeSampleRadius t))

def normalizedProjectiveHorizontalCorrection
    (t alpha q : ℝ) : ℝ :=
  normalizedCenteredHorizontalCorrectionAtScale t 2 alpha q
      * onLineRadiusProfile (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t)
    - normalizedCenteredHorizontalCorrectionAtScale t 1 alpha q
      * onLineRadiusProfile (quantitativeCanonicalTaper t)
          (2 * quantitativeSampleRadius t)
    + normalizedRadiusZeroHorizontalCorrection t alpha q
      * (onLineRadiusProfile (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t)
          - onLineRadiusProfile (quantitativeCanonicalTaper t)
            (2 * quantitativeSampleRadius t))

/-- Exact same-object horizontal split of one normalized projective atom. -/
theorem normalizedProjectiveOffZeroAtom_eq_base_add_horizontal
    (t : ℝ) (rho : Zeros) :
    normalizedProjectiveOffZeroAtom t rho
      =
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * normalizedProjectiveBaseTransform t (normalizedGap t rho)
      +
    ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
      * normalizedProjectiveHorizontalCorrection t
          (normalizedHorizontalHeight t rho) (normalizedGap t rho) := by
  rw [normalizedCenteredZeroAtomAtScale_eq_base_add_horizontal t 2 rho,
      normalizedCenteredZeroAtomAtScale_eq_base_add_horizontal t 1 rho,
      normalizedRadiusZeroZeroAtom_eq_base_add_horizontal t rho]
  unfold normalizedProjectiveOffZeroAtom
    normalizedProjectiveBaseTransform
    normalizedProjectiveHorizontalCorrection
  ring

/-- Finite projective atoms split into the q-only Stieltjes surface plus the
horizontal correction, with no absolute value or estimate. -/
theorem sum_normalizedProjectiveOffZeroAtom_eq_base_add_horizontal
    (t : ℝ) (F : Finset Zeros) :
    (∑ rho ∈ F, normalizedProjectiveOffZeroAtom t rho)
      =
    (∑ rho ∈ F,
      ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
        * normalizedProjectiveBaseTransform t (normalizedGap t rho))
      +
    (∑ rho ∈ F,
      ((zetaZeroConfig).mult (rho : ℂ) : ℝ)
        * normalizedProjectiveHorizontalCorrection t
            (normalizedHorizontalHeight t rho) (normalizedGap t rho)) := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro rho hrho
  exact normalizedProjectiveOffZeroAtom_eq_base_add_horizontal t rho

end Synthesis
