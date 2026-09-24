import Synthesis.RiemannNormalizedProjectiveOffHorizontalSplit
import Synthesis.RiemannNormalizedCenteredProfileSpectralGap
import Synthesis.RiemannNormalizedRvMZeroModeFourier

/-!
# Projective-native normalized base profile

The normalized projective Off base transform is not intrinsically a three-piece
object.  Expanding the centered definitions inside the determinant cancels the
radius-zero constants exactly and leaves one physical profile

  P_t(v)
    = 4 G_t(v)
        (A0(r) cos(v/8) - A0(2r) cos(v/16)),

where G_t is the fixed normalized canonical taper and r=t/16.

Thus the q-only projective Stieltjes observable is exactly the cosine transform

  Phi_proj(q) = integral P_t(v) cos(qv) dv.

This is the consumer-sufficient quotient form: the downstream projective
consumer sees one symmetry-reduced profile, not three separately estimated
radius channels.

Since G_t is supported away from zero, P_t inherits the same open gap

  |v| <= 3*pi/4 -> P_t(v)=0.

Consequently its complexification has value zero at v=0, so the existing
Fourier-inversion compiler annihilates a constant spectral density as soon as
the Fourier transform is placed in L1.  The remaining bridge from this
whole-line Fourier statement to the literal normalized RvM/Stieltjes carrier is
kept explicit.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

def normalizedProjectivePhysicalProfile (t v : ℝ) : ℝ :=
  4 * normalizedCanonicalFixedProfile t v *
    (onLineRadiusProfile (quantitativeCanonicalTaper t)
        (quantitativeSampleRadius t) * Real.cos (v / 8)
      -
     onLineRadiusProfile (quantitativeCanonicalTaper t)
        (2 * quantitativeSampleRadius t) * Real.cos (v / 16))

theorem normalizedCanonicalFixedProfile_zero_of_abs_le
    (t v : ℝ) (hv : |v| <= 3 * Real.pi / 4) :
    normalizedCanonicalFixedProfile t v = 0 := by
  by_contra hne
  have hgap := normalizedCanonicalFixedProfile_support_gap (t := t) hne
  linarith

theorem normalizedProjectivePhysicalProfile_zero_of_abs_le
    (t v : ℝ) (hv : |v| <= 3 * Real.pi / 4) :
    normalizedProjectivePhysicalProfile t v = 0 := by
  unfold normalizedProjectivePhysicalProfile
  rw [normalizedCanonicalFixedProfile_zero_of_abs_le t v hv]
  ring

theorem normalizedProjectivePhysicalProfile_zero (t : ℝ) :
    normalizedProjectivePhysicalProfile t 0 = 0 := by
  apply normalizedProjectivePhysicalProfile_zero_of_abs_le
  simp only [abs_zero]
  positivity

theorem normalizedProjectivePhysicalProfile_continuous (t : ℝ) :
    Continuous (normalizedProjectivePhysicalProfile t) := by
  unfold normalizedProjectivePhysicalProfile
  fun_prop

theorem normalizedProjectivePhysicalProfile_compact (t : ℝ) :
    HasCompactSupport (normalizedProjectivePhysicalProfile t) := by
  unfold normalizedProjectivePhysicalProfile
  exact ((normalizedCanonicalFixedProfile_compact t).mul_left).mul_right

theorem normalizedProjectivePhysicalProfile_integrable (t : ℝ) :
    Integrable (normalizedProjectivePhysicalProfile t) := by
  exact (normalizedProjectivePhysicalProfile_continuous t)
    .integrable_of_hasCompactSupport
      (normalizedProjectivePhysicalProfile_compact t)

/--
Pointwise algebraic collapse of the three projective base pieces to the single
projective physical profile.
-/
theorem normalizedProjective_base_integrand_collapse
    (t q v : ℝ) :
    4 * normalizedCenteredFixedProfileAtScale t 2 v * Real.cos (q*v)
        * onLineRadiusProfile (quantitativeCanonicalTaper t)
            (quantitativeSampleRadius t)
      -
      4 * normalizedCenteredFixedProfileAtScale t 1 v * Real.cos (q*v)
        * onLineRadiusProfile (quantitativeCanonicalTaper t)
            (2 * quantitativeSampleRadius t)
      +
      4 * normalizedCanonicalFixedProfile t v * Real.cos (q*v)
        * (onLineRadiusProfile (quantitativeCanonicalTaper t)
              (quantitativeSampleRadius t)
            -
           onLineRadiusProfile (quantitativeCanonicalTaper t)
              (2 * quantitativeSampleRadius t))
      =
      normalizedProjectivePhysicalProfile t v * Real.cos (q*v) := by
  unfold normalizedCenteredFixedProfileAtScale
    normalizedProjectivePhysicalProfile
  ring

/--
The q-only projective Stieltjes observable is exactly the cosine transform of
the single projective physical profile.
-/
theorem normalizedProjectiveBaseTransform_eq_physicalCosine
    (t q : ℝ) :
    normalizedProjectiveBaseTransform t q
      =
    ∫ v : ℝ,
      normalizedProjectivePhysicalProfile t v * Real.cos (q*v) := by
  let A : ℝ :=
    onLineRadiusProfile (quantitativeCanonicalTaper t)
      (quantitativeSampleRadius t)
  let B : ℝ :=
    onLineRadiusProfile (quantitativeCanonicalTaper t)
      (2 * quantitativeSampleRadius t)
  let f2 : ℝ → ℝ := fun v =>
    4 * normalizedCenteredFixedProfileAtScale t 2 v * Real.cos (q*v)
  let f1 : ℝ → ℝ := fun v =>
    4 * normalizedCenteredFixedProfileAtScale t 1 v * Real.cos (q*v)
  let f0 : ℝ → ℝ := fun v =>
    4 * normalizedCanonicalFixedProfile t v * Real.cos (q*v)

  have hf2 : Integrable f2 := by
    dsimp [f2]
    exact Continuous.integrable_of_hasCompactSupport
      (by unfold normalizedCenteredFixedProfileAtScale; fun_prop)
      (((normalizedCanonicalFixedProfile_compact t).mul_right.mul_left).mul_right)
  have hf1 : Integrable f1 := by
    dsimp [f1]
    exact Continuous.integrable_of_hasCompactSupport
      (by unfold normalizedCenteredFixedProfileAtScale; fun_prop)
      (((normalizedCanonicalFixedProfile_compact t).mul_right.mul_left).mul_right)
  have hf0 : Integrable f0 := by
    dsimp [f0]
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((normalizedCanonicalFixedProfile_compact t).mul_left.mul_right)

  have hcombine :
      A * (∫ v : ℝ, f2 v)
        - B * (∫ v : ℝ, f1 v)
        + (A-B) * (∫ v : ℝ, f0 v)
      =
      ∫ v : ℝ, A * f2 v - B * f1 v + (A-B) * f0 v := by
    rw [integral_add ((hf2.const_mul A).sub (hf1.const_mul B))
          (hf0.const_mul (A-B))]
    rw [integral_sub (hf2.const_mul A) (hf1.const_mul B)]
    rw [integral_const_mul, integral_const_mul, integral_const_mul]

  calc
    normalizedProjectiveBaseTransform t q
        =
      A * (∫ v : ℝ, f2 v)
        - B * (∫ v : ℝ, f1 v)
        + (A-B) * (∫ v : ℝ, f0 v) := by
          unfold normalizedProjectiveBaseTransform
            normalizedCenteredBaseTransformAtScale
            normalizedRadiusZeroBaseTransform
          dsimp [A, B, f2, f1, f0]
          ring
    _ = ∫ v : ℝ, A * f2 v - B * f1 v + (A-B) * f0 v := hcombine
    _ = ∫ v : ℝ,
          normalizedProjectivePhysicalProfile t v * Real.cos (q*v) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun v => by
            dsimp [A, B, f2, f1, f0]
            rw [← normalizedProjective_base_integrand_collapse t q v]
            ring

def normalizedProjectiveComplexProfile (t : ℝ) : ℝ → ℂ :=
  fun v => (normalizedProjectivePhysicalProfile t v : ℝ)

theorem normalizedProjectiveComplexProfile_continuous (t : ℝ) :
    Continuous (normalizedProjectiveComplexProfile t) := by
  unfold normalizedProjectiveComplexProfile
  fun_prop

theorem normalizedProjectiveComplexProfile_compact (t : ℝ) :
    HasCompactSupport (normalizedProjectiveComplexProfile t) := by
  apply HasCompactSupport.intro
    (K := tsupport (normalizedProjectivePhysicalProfile t))
    (normalizedProjectivePhysicalProfile_compact t)
  intro x hx
  have hzero :
      normalizedProjectivePhysicalProfile t x = 0 :=
    image_eq_zero_of_notMem_tsupport hx
  simp [normalizedProjectiveComplexProfile, hzero]

theorem normalizedProjectiveComplexProfile_integrable (t : ℝ) :
    Integrable (normalizedProjectiveComplexProfile t) := by
  exact (normalizedProjectiveComplexProfile_continuous t)
    .integrable_of_hasCompactSupport
      (normalizedProjectiveComplexProfile_compact t)

theorem normalizedProjectiveComplexProfile_zero (t : ℝ) :
    normalizedProjectiveComplexProfile t 0 = 0 := by
  simp [normalizedProjectiveComplexProfile,
    normalizedProjectivePhysicalProfile_zero]

/--
Projective-native whole-line constant-density annihilation.

This is intentionally conditional only on Fourier L1, matching the existing
centered Fourier compiler.  The actual q-grid / RvM same-object attachment is
still a separate theorem obligation.
-/
theorem normalizedProjectiveComplexProfile_fourier_total_zero
    (t : ℝ)
    (hfourier :
      Integrable
        (FourierTransform.fourier
          (normalizedProjectiveComplexProfile t))) :
    (∫ w : ℝ,
      FourierTransform.fourier
        (normalizedProjectiveComplexProfile t) w) = 0 := by
  exact integral_fourier_eq_zero_of_value_zero
    (normalizedProjectiveComplexProfile_continuous t)
    (normalizedProjectiveComplexProfile_integrable t)
    hfourier
    (normalizedProjectiveComplexProfile_zero t)

end Synthesis
