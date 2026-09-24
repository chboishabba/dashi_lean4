import Synthesis.RiemannNormalizedCanonicalFixedProfile
import Zeta23Bridge.OscillatoryKernelDecay

/-!
# Fixed-profile oscillatory decay for the normalized H2 shell

After normalization the centered canonical taper has fixed compact support and
frequency q = delta/t.  This file applies the repository's existing signed
oscillatory integration-by-parts theorem directly in the normalized variable.

The result is the first theorem-facing H2d estimate:

  | integral 4 H_t(v) cosh(alpha v) cos(q v) dv |
    <= C_norm(t,alpha) / q^2,

for q != 0, where H_t is the exact normalized centered canonical taper.

Unlike the old u-coordinate estimate, the derivative constant is taken on the
fixed v-profile.  No shrinking-support t-growth is introduced by the change of
variables.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

open Zeta23Bridge.OscillatoryKernelDecay

def normalizedPairWeight (t alpha : ℝ) : ℝ → ℝ :=
  fun v => 4 * normalizedCenteredFixedProfile t v * Real.cosh (alpha * v)

def normalizedPairCurvature (t alpha : ℝ) : ℝ :=
  ∫ v : ℝ, |deriv (deriv (normalizedPairWeight t alpha)) v|

theorem normalizedInnerFixedProfile_eq_symBump :
    normalizedInnerFixedProfile
      = quantitativeSymBump Real.pi (Real.pi / 4) := by
  funext v
  unfold normalizedInnerFixedProfile quantitativeSymBump symmetrize scaledUnitBump
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  congr 1
  · congr 1
    field_simp [hp]
    ring
  · congr 1
    field_simp [hp]
    ring

theorem normalizedOuterFixedProfile_eq_symBump :
    normalizedOuterFixedProfile
      = quantitativeSymBump (2 * Real.pi) (Real.pi / 4) := by
  funext v
  unfold normalizedOuterFixedProfile quantitativeSymBump symmetrize scaledUnitBump
  have hp : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  congr 1
  · congr 1
    field_simp [hp]
    ring
  · congr 1
    field_simp [hp]
    ring

theorem normalizedInnerFixedProfile_contDiff :
    ContDiff ℝ 2 normalizedInnerFixedProfile := by
  rw [normalizedInnerFixedProfile_eq_symBump]
  exact quantitativeSymBump_contDiff (by positivity)

theorem normalizedOuterFixedProfile_contDiff :
    ContDiff ℝ 2 normalizedOuterFixedProfile := by
  rw [normalizedOuterFixedProfile_eq_symBump]
  exact quantitativeSymBump_contDiff (by positivity)

theorem normalizedInnerFixedProfile_compact :
    HasCompactSupport normalizedInnerFixedProfile := by
  rw [normalizedInnerFixedProfile_eq_symBump]
  exact quantitativeSymBump_hasCompactSupport (by positivity)

theorem normalizedOuterFixedProfile_compact :
    HasCompactSupport normalizedOuterFixedProfile := by
  rw [normalizedOuterFixedProfile_eq_symBump]
  exact quantitativeSymBump_hasCompactSupport (by positivity)

theorem normalizedCanonicalFixedProfile_contDiff (t : ℝ) :
    ContDiff ℝ 2 (normalizedCanonicalFixedProfile t) := by
  unfold normalizedCanonicalFixedProfile
  exact normalizedInnerFixedProfile_contDiff.add
    (contDiff_const.mul normalizedOuterFixedProfile_contDiff)

theorem normalizedCanonicalFixedProfile_compact (t : ℝ) :
    HasCompactSupport (normalizedCanonicalFixedProfile t) := by
  unfold normalizedCanonicalFixedProfile
  exact normalizedInnerFixedProfile_compact.add
    normalizedOuterFixedProfile_compact.mul_left

theorem normalizedCenteredFixedProfile_contDiff (t : ℝ) :
    ContDiff ℝ 2 (normalizedCenteredFixedProfile t) := by
  unfold normalizedCenteredFixedProfile
  exact (normalizedCanonicalFixedProfile_contDiff t).mul (by fun_prop)

theorem normalizedCenteredFixedProfile_compact (t : ℝ) :
    HasCompactSupport (normalizedCenteredFixedProfile t) := by
  unfold normalizedCenteredFixedProfile
  exact (normalizedCanonicalFixedProfile_compact t).mul_right

theorem normalizedPairWeight_contDiff (t alpha : ℝ) :
    ContDiff ℝ 2 (normalizedPairWeight t alpha) := by
  unfold normalizedPairWeight
  exact (contDiff_const.mul (normalizedCenteredFixedProfile_contDiff t)).mul
    (by fun_prop)

theorem normalizedPairWeight_compact (t alpha : ℝ) :
    HasCompactSupport (normalizedPairWeight t alpha) := by
  unfold normalizedPairWeight
  exact (normalizedCenteredFixedProfile_compact t).mul_left.mul_right

theorem normalizedPairKernel_eq_pairWeight_mul_cos
    (t alpha q v : ℝ) :
    4 * normalizedCenteredFixedProfile t v
        * Real.cosh (alpha * v) * Real.cos (q * v)
      =
    normalizedPairWeight t alpha v * Real.cos (q * v) := by
  unfold normalizedPairWeight
  ring

/--
Normalized per-frequency H2d decay.  This is the exact fixed-profile analogue of
the old delta-coordinate 1/delta^2 estimate.
-/
theorem abs_integral_normalizedCenteredPair_le
    {t alpha q : ℝ} (hq : q ≠ 0) :
    |∫ v : ℝ,
      4 * normalizedCenteredFixedProfile t v
        * Real.cosh (alpha * v) * Real.cos (q * v)|
      <= normalizedPairCurvature t alpha / q ^ 2 := by
  have hrw :
      (∫ v : ℝ,
        4 * normalizedCenteredFixedProfile t v
          * Real.cosh (alpha * v) * Real.cos (q * v))
      =
      ∫ v : ℝ, normalizedPairWeight t alpha v * Real.cos (q * v) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v =>
      normalizedPairKernel_eq_pairWeight_mul_cos t alpha q v
  rw [hrw]
  exact abs_integral_mul_cos_le
    (normalizedPairWeight_contDiff t alpha)
    (normalizedPairWeight_compact t alpha)
    hq

/--
Same estimate on the literal centered reflection-pair integral, after the exact
v=tu normalization and delta=q*t substitution.
-/
theorem abs_integral_reflectionPair_centeredCanonical_gap_q_le
    {t a delta q : ℝ}
    (ht : 0 < t)
    (hq : delta = q * t)
    (hq0 : q ≠ 0) :
    |∫ u : ℝ,
      Zeta23Bridge.LiteralWeilOffOrdinateReflectionPair.reflectionPairWeight
        (gammaCenteredTaper
          (quantitativeCanonicalTaper t)
          (quantitativeSampleRadius t))
        a delta u|
      <=
    (1 / t) *
      (normalizedPairCurvature t (a / t) / q ^ 2) := by
  rw [integral_reflectionPairWeight_centeredCanonical_gap_q ht hq]
  rw [abs_mul, abs_of_pos (by positivity : 0 < (1 / t : ℝ))]
  have hfixed :
      (fun v : ℝ =>
        4 * normalizedCenteredCanonicalTaper t v
          * Real.cosh ((a / t) * v)
          * Real.cos (q * v))
      =
      fun v : ℝ =>
        4 * normalizedCenteredFixedProfile t v
          * Real.cosh ((a / t) * v)
          * Real.cos (q * v) := by
    funext v
    rw [normalizedCenteredCanonicalTaper_eq_fixedProfile ht]
  rw [hfixed]
  exact mul_le_mul_of_nonneg_left
    (abs_integral_normalizedCenteredPair_le
      (t := t) (alpha := a / t) hq0)
    (by positivity)

end Synthesis
