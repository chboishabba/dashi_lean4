import Synthesis.RiemannGammaCanonicalRatioGap
import Synthesis.RiemannQuantitativeCanonicalTaper

/-!
# Integrated matched-bump Gamma/pole ratio gap

This file pays H1 at the explicit kernel-density level.

On the positive coordinate, define the selected-radius pole density

    p_t(u) = psi_inner(u) * cosh(u/2) * cos(tu) * cos((t/16)u).

It is negative on the inner window.  The matched outer point is u+pi/t, and
because the same affine bump shape is used in both windows, the outer bump value
equals the inner bump value at matched coordinates.

The Gamma/pole ratio gap is uniformly at least canonicalGammaRatioGap t, so
after multiplying by the positive magnitude -p_t(u) and integrating,

    (-P_in) * d(t)
      <= G_in + lambda * G_out

once the pole-cancellation coefficient is used.

This module isolates the measure-theoretic part independently of the remaining
literal Gamma-kernel bridge.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

def innerPositiveBump (t : ℝ) : ℝ → ℝ :=
  scaledUnitBump (quantitativeTaperInnerCenter t) (quantitativeTaperR t)

def outerPositiveBump (t : ℝ) : ℝ → ℝ :=
  scaledUnitBump (quantitativeTaperOuterCenter t) (quantitativeTaperR t)

def innerPoleDensity (t u : ℝ) : ℝ :=
  innerPositiveBump t u
    * quantitativePoleWeight t (quantitativeSampleRadius t) u

def outerPoleDensity (t u : ℝ) : ℝ :=
  outerPositiveBump t u
    * quantitativePoleWeight t (quantitativeSampleRadius t) u

def innerGammaKernelDensity (t u : ℝ) : ℝ :=
  gammaToPoleRatio t u * innerPoleDensity t u

def outerGammaKernelDensity (t u : ℝ) : ℝ :=
  gammaToPoleRatio t u * outerPoleDensity t u

theorem outerPositiveBump_matched
    {t u : ℝ} (ht : 0 < t) :
    outerPositiveBump t (u + Real.pi/t) = innerPositiveBump t u := by
  unfold outerPositiveBump innerPositiveBump scaledUnitBump
  unfold quantitativeTaperOuterCenter quantitativeTaperInnerCenter
  have ht0 : t ≠ 0 := ne_of_gt ht
  congr 1
  field_simp [ht0]
  ring

theorem matched_pole_weight_cos_relation
    {t u : ℝ} (ht : 0 < t) :
    Real.cos (t * (u + Real.pi/t)) = - Real.cos (t*u) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hphase : t * (u + Real.pi/t) = t*u + Real.pi := by
    field_simp [ht0]
    ring
  rw [hphase, Real.cos_add_pi]

theorem innerPoleDensity_nonpos_on_window
    {t u : ℝ} (ht : 18 <= t)
    (huLower : 3 * Real.pi/(4*t) <= u)
    (huUpper : u <= 5 * Real.pi/(4*t)) :
    innerPoleDensity t u <= 0 := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  unfold innerPoleDensity innerPositiveBump quantitativePoleWeight
  have hb : 0 <= scaledUnitBump
      (quantitativeTaperInnerCenter t) (quantitativeTaperR t) u :=
    scaledUnitBump_nonneg _ _ _
  have hcos : Real.cos (t*u) <= 0 := by
    have hlo : 3 * Real.pi/4 <= t*u := by
      have h := mul_le_mul_of_nonneg_left huLower ht0.le
      field_simp [ne_of_gt ht0] at h
      nlinarith [Real.pi_pos]
    have hhi : t*u <= 5 * Real.pi/4 := by
      have h := mul_le_mul_of_nonneg_left huUpper ht0.le
      field_simp [ne_of_gt ht0] at h
      nlinarith [Real.pi_pos]
    have hs : 0 <= Real.cos (t*u - Real.pi) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor <;> linarith [Real.pi_pos]
    rw [Real.cos_sub_pi] at hs
    linarith
  have hsample : 0 < Real.cos ((t/16)*u) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have hu0 : 0 < u := lt_of_lt_of_le (by positivity) huLower
      nlinarith
    · have h := mul_le_mul_of_nonneg_left huUpper
        (show 0 <= t/16 by positivity)
      field_simp [ne_of_gt ht0] at h
      nlinarith [Real.pi_pos]
  have hch : 0 < Real.cosh (u/2) := Real.cosh_pos _
  exact mul_nonpos_of_nonneg_of_nonpos hb
    (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hch.le hcos)
      hsample.le)

theorem canonical_gap_times_innerPoleMagnitude_le_pointwise
    {t u : ℝ} (ht : 18 <= t)
    (huLower : 3 * Real.pi/(4*t) <= u)
    (huUpper : u <= 5 * Real.pi/(4*t)) :
    canonicalGammaRatioGap t * (- innerPoleDensity t u)
      <=
    (gammaToPoleRatio t (u + Real.pi/t)
      - gammaToPoleRatio t u) * (- innerPoleDensity t u) := by
  have hgap :=
    canonicalGammaRatioGap_le_matched_gap ht huLower huUpper
  have hmag : 0 <= - innerPoleDensity t u :=
    neg_nonneg.mpr (innerPoleDensity_nonpos_on_window ht huLower huUpper)
  exact mul_le_mul_of_nonneg_right hgap hmag

/--
Integrated H1 lemma.

Any integrable matched-coordinate pole magnitude supported in the canonical
inner window inherits the same explicit ratio gap.
-/
theorem integrated_canonicalRatioGap
    {t : ℝ} (ht : 18 <= t)
    {w : ℝ → ℝ}
    (hw : Integrable w)
    (hnn : ∀ u, 0 <= w u)
    (hsupp : ∀ u, w u ≠ 0 →
      3 * Real.pi/(4*t) <= u ∧ u <= 5 * Real.pi/(4*t)) :
    canonicalGammaRatioGap t * (∫ u : ℝ, w u)
      <=
    ∫ u : ℝ,
      (gammaToPoleRatio t (u + Real.pi/t)
        - gammaToPoleRatio t u) * w u := by
  have hgap : 0 <= canonicalGammaRatioGap t :=
    canonicalGammaRatioGap_nonneg ht
  have hleft : Integrable
      (fun u : ℝ => canonicalGammaRatioGap t * w u) :=
    hw.const_mul _
  have hright : Integrable
      (fun u : ℝ =>
        (gammaToPoleRatio t (u + Real.pi/t)
          - gammaToPoleRatio t u) * w u) := by
    -- compact-support applications below provide this directly; keep the
    -- generic theorem honest by deriving it from bounded support.
    have hcontRatio :
        ContinuousOn
          (fun u : ℝ =>
            gammaToPoleRatio t (u + Real.pi/t)
              - gammaToPoleRatio t u)
          (Set.Icc (3 * Real.pi/(4*t)) (5 * Real.pi/(4*t))) := by
      fun_prop
    have hcompact : IsCompact
        (Set.Icc (3 * Real.pi/(4*t)) (5 * Real.pi/(4*t))) :=
      isCompact_Icc
    obtain ⟨C, hC⟩ := hcompact.bddAbove_image hcontRatio.continuousOn.norm
    -- Rather than expose the bound, use compact support inherited from hsupp.
    have hwsupp : HasCompactSupport w := by
      refine ⟨Set.Icc (3 * Real.pi/(4*t)) (5 * Real.pi/(4*t)),
        isCompact_Icc, ?_⟩
      intro u hu
      by_contra hne
      have hs := hsupp u hne
      exact hu hs
    exact ((continuousOn_iff_continuous_restrict.mp hcontRatio).mul
      hw.stronglyMeasurable.continuousOn).integrable_of_hasCompactSupport
      hwsupp
  have hpoint : ∀ u,
      canonicalGammaRatioGap t * w u
        <=
      (gammaToPoleRatio t (u + Real.pi/t)
        - gammaToPoleRatio t u) * w u := by
    intro u
    by_cases hwu : w u = 0
    · simp [hwu]
    · have hs := hsupp u hwu
      exact mul_le_mul_of_nonneg_right
        (canonicalGammaRatioGap_le_matched_gap ht hs.1 hs.2)
        (hnn u)
  have h := integral_mono hleft hright hpoint
  rw [integral_const_mul] at h
  exact h

end Synthesis
