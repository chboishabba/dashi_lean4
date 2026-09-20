import Synthesis.RiemannNormalizedProjectiveBaseTransformDerivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Regularity of the projective base derivative

The exact projective base derivative is itself a compact-profile sine transform.
Its variation is controlled by the second absolute moment of the same physical
profile.  Thus the derivative is globally Lipschitz, hence continuous, and the
physical-ordinate derivative is interval-integrable on every finite window.

This closes the regularity hypothesis needed to instantiate the exact literal
N-mu Abel identity with the actual projective consumer.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

def normalizedProjectiveProfileSecondMoment (t : ℝ) : ℝ :=
  ∫ v : ℝ,
    |normalizedProjectivePhysicalProfile t v| * |v| ^ 2

theorem normalizedProjectiveProfileSecondMoment_nonneg (t : ℝ) :
    0 ≤ normalizedProjectiveProfileSecondMoment t := by
  unfold normalizedProjectiveProfileSecondMoment
  positivity

theorem normalizedProjectiveProfile_secondMoment_integrable (t : ℝ) :
    Integrable
      (fun v : ℝ =>
        |normalizedProjectivePhysicalProfile t v| * |v| ^ 2) := by
  exact
    ((normalizedProjectivePhysicalProfile_continuous t).abs.mul
      (continuous_abs.pow 2))
      .integrable_of_hasCompactSupport
        ((normalizedProjectivePhysicalProfile_compact t).abs.mul_right)

theorem normalizedProjectiveBaseTransformDeriv_lipschitz
    (t p q : ℝ) :
    |normalizedProjectiveBaseTransformDeriv t q
      - normalizedProjectiveBaseTransformDeriv t p|
      ≤
    normalizedProjectiveProfileSecondMoment t * |q - p| := by
  unfold normalizedProjectiveBaseTransformDeriv
  have hiq :
      Integrable
        (fun v : ℝ =>
          - normalizedProjectivePhysicalProfile t v
            * Real.sin (q * v) * v) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      (((normalizedProjectivePhysicalProfile_compact t).neg.mul_right).mul_right)
  have hip :
      Integrable
        (fun v : ℝ =>
          - normalizedProjectivePhysicalProfile t v
            * Real.sin (p * v) * v) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      (((normalizedProjectivePhysicalProfile_compact t).neg.mul_right).mul_right)
  rw [← integral_sub hiq hip]
  have hdom :
      Integrable
        (fun v : ℝ =>
          |q-p| *
            (|normalizedProjectivePhysicalProfile t v| * |v| ^ 2)) :=
    (normalizedProjectiveProfile_secondMoment_integrable t).const_mul |q-p|
  calc
    |∫ v : ℝ,
      (- normalizedProjectivePhysicalProfile t v
          * Real.sin (q*v) * v
        -
       (- normalizedProjectivePhysicalProfile t v
          * Real.sin (p*v) * v))|
      ≤
    ∫ v : ℝ,
      |(- normalizedProjectivePhysicalProfile t v
          * Real.sin (q*v) * v
        -
       (- normalizedProjectivePhysicalProfile t v
          * Real.sin (p*v) * v))| :=
      abs_integral_le_integral_abs
    _ ≤
    ∫ v : ℝ,
      |q-p| *
        (|normalizedProjectivePhysicalProfile t v| * |v| ^ 2) := by
      apply integral_mono (hiq.sub hip).abs hdom
      intro v
      have hs := Real.abs_sin_sub_sin_le (q*v) (p*v)
      have hfactor : |q*v-p*v| = |q-p| * |v| := by
        rw [← sub_mul, abs_mul]
      calc
        |(- normalizedProjectivePhysicalProfile t v
            * Real.sin (q*v) * v
          -
         (- normalizedProjectivePhysicalProfile t v
            * Real.sin (p*v) * v))|
          =
        |normalizedProjectivePhysicalProfile t v|
          * |Real.sin (q*v)-Real.sin (p*v)| * |v| := by
            ring_nf
            rw [abs_mul, abs_mul, abs_neg]
        _ ≤
        |normalizedProjectivePhysicalProfile t v|
          * |q*v-p*v| * |v| := by
            gcongr
        _ =
        |q-p| *
          (|normalizedProjectivePhysicalProfile t v| * |v| ^ 2) := by
            rw [hfactor]
            ring
    _ =
      |q-p| * normalizedProjectiveProfileSecondMoment t := by
        rw [integral_const_mul]
        rfl
    _ =
      normalizedProjectiveProfileSecondMoment t * |q-p| := by ring

theorem normalizedProjectiveBaseTransformDeriv_continuous
    (t : ℝ) :
    Continuous (normalizedProjectiveBaseTransformDeriv t) := by
  apply continuous_iff_continuousAt.2
  intro q
  apply continuousAt_of_locally_lipschitz
  refine ⟨normalizedProjectiveProfileSecondMoment t, ?_⟩
  filter_upwards with p
  simpa [Real.dist_eq] using
    normalizedProjectiveBaseTransformDeriv_lipschitz t q p

theorem normalizedProjectiveOrdinateTestDeriv_continuous
    {t : ℝ} (ht : t ≠ 0) :
    Continuous (normalizedProjectiveOrdinateTestDeriv t) := by
  unfold normalizedProjectiveOrdinateTestDeriv
  fun_prop

theorem normalizedProjectiveOrdinateTestDeriv_intervalIntegrable
    {t A B : ℝ} (ht : t ≠ 0) :
    IntervalIntegrable
      (normalizedProjectiveOrdinateTestDeriv t) volume A B :=
  (normalizedProjectiveOrdinateTestDeriv_continuous ht)
    .intervalIntegrable A B

end Synthesis
