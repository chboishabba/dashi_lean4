import Synthesis.RiemannNormalizedProjectiveRvMConsumer
import Synthesis.RiemannNormalizedCountingAbelCompiler
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Abel variation for the exact projective base transform

This is the projective analogue of `RiemannNormalizedBaseTransformVariation`.
It deliberately uses the literal projective physical profile itself rather than
re-expanding it into the older centered radius channels.

Let

  Phi_proj(t,q) = integral P_t(v) cos(q v) dv.

Define the exact L1 mass and first absolute moment

  M0(t) = integral |P_t(v)|,
  M1(t) = integral |P_t(v)| |v|.

Then

  |Phi_proj(t,q)| <= M0(t)

and

  |Phi_proj(t,q)-Phi_proj(t,p)| <= M1(t) |q-p|.

Hence on every increasing finite grid starting at zero,

  AbelVariation(Phi_proj) <= M0(t) + M1(t) Q.

No RvM estimate and no quadrature approximation enters here.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

def normalizedProjectiveProfileL1 (t : ℝ) : ℝ :=
  ∫ v : ℝ, |normalizedProjectivePhysicalProfile t v|

def normalizedProjectiveProfileFirstMoment (t : ℝ) : ℝ :=
  ∫ v : ℝ, |normalizedProjectivePhysicalProfile t v| * |v|

theorem normalizedProjectiveProfileL1_nonneg (t : ℝ) :
    0 <= normalizedProjectiveProfileL1 t := by
  unfold normalizedProjectiveProfileL1
  positivity

theorem normalizedProjectiveProfileFirstMoment_nonneg (t : ℝ) :
    0 <= normalizedProjectiveProfileFirstMoment t := by
  unfold normalizedProjectiveProfileFirstMoment
  positivity

theorem normalizedProjectiveProfile_abs_integrable (t : ℝ) :
    Integrable (fun v : ℝ => |normalizedProjectivePhysicalProfile t v|) := by
  exact (normalizedProjectivePhysicalProfile_integrable t).abs

theorem normalizedProjectiveProfile_firstMoment_integrable (t : ℝ) :
    Integrable
      (fun v : ℝ =>
        |normalizedProjectivePhysicalProfile t v| * |v|) := by
  exact
    ((normalizedProjectivePhysicalProfile_continuous t).abs.mul continuous_abs)
      .integrable_of_hasCompactSupport
        ((normalizedProjectivePhysicalProfile_compact t).abs.mul_right)

theorem normalizedProjectiveBaseTransform_abs_le_profileL1
    (t q : ℝ) :
    |normalizedProjectiveBaseTransform t q|
      <= normalizedProjectiveProfileL1 t := by
  rw [normalizedProjectiveBaseTransform_eq_physicalCosine]
  calc
    |∫ v : ℝ,
      normalizedProjectivePhysicalProfile t v * Real.cos (q * v)|
      <=
    ∫ v : ℝ,
      |normalizedProjectivePhysicalProfile t v * Real.cos (q * v)| :=
        abs_integral_le_integral_abs
    _ <=
    ∫ v : ℝ, |normalizedProjectivePhysicalProfile t v| := by
      apply integral_mono
      · exact
          (Continuous.integrable_of_hasCompactSupport
            (by fun_prop)
            ((normalizedProjectivePhysicalProfile_compact t).mul_right)).abs
      · exact normalizedProjectiveProfile_abs_integrable t
      · intro v
        rw [abs_mul]
        have hc := Real.abs_cos_le_one (q * v)
        exact mul_le_of_le_one_right (abs_nonneg _) hc
    _ = normalizedProjectiveProfileL1 t := rfl

theorem normalizedProjectiveBaseTransform_lipschitz
    (t p q : ℝ) :
    |normalizedProjectiveBaseTransform t q
      - normalizedProjectiveBaseTransform t p|
      <=
    normalizedProjectiveProfileFirstMoment t * |q - p| := by
  rw [normalizedProjectiveBaseTransform_eq_physicalCosine,
      normalizedProjectiveBaseTransform_eq_physicalCosine]
  have hiq :
      Integrable
        (fun v : ℝ =>
          normalizedProjectivePhysicalProfile t v * Real.cos (q * v)) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((normalizedProjectivePhysicalProfile_compact t).mul_right)
  have hip :
      Integrable
        (fun v : ℝ =>
          normalizedProjectivePhysicalProfile t v * Real.cos (p * v)) := by
    exact Continuous.integrable_of_hasCompactSupport
      (by fun_prop)
      ((normalizedProjectivePhysicalProfile_compact t).mul_right)
  rw [← integral_sub hiq hip]
  have hdom :
      Integrable
        (fun v : ℝ =>
          |q-p| *
            (|normalizedProjectivePhysicalProfile t v| * |v|)) :=
    (normalizedProjectiveProfile_firstMoment_integrable t).const_mul |q-p|
  calc
    |∫ v : ℝ,
      (normalizedProjectivePhysicalProfile t v * Real.cos (q*v)
        - normalizedProjectivePhysicalProfile t v * Real.cos (p*v))|
      <=
    ∫ v : ℝ,
      |normalizedProjectivePhysicalProfile t v * Real.cos (q*v)
        - normalizedProjectivePhysicalProfile t v * Real.cos (p*v)| :=
        abs_integral_le_integral_abs
    _ <=
    ∫ v : ℝ,
      |q-p| *
        (|normalizedProjectivePhysicalProfile t v| * |v|) := by
      apply integral_mono (hiq.sub hip).abs hdom
      intro v
      have hc := Real.abs_cos_sub_cos_le (q*v) (p*v)
      have hfactor : |q*v-p*v| = |q-p| * |v| := by
        rw [← sub_mul, abs_mul]
      calc
        |normalizedProjectivePhysicalProfile t v * Real.cos (q*v)
          - normalizedProjectivePhysicalProfile t v * Real.cos (p*v)|
          =
        |normalizedProjectivePhysicalProfile t v|
          * |Real.cos (q*v)-Real.cos (p*v)| := by
            rw [← mul_sub, abs_mul]
        _ <=
        |normalizedProjectivePhysicalProfile t v| * |q*v-p*v| := by
          gcongr
        _ =
        |q-p| *
          (|normalizedProjectivePhysicalProfile t v| * |v|) := by
            rw [hfactor]
            ring
    _ =
      |q-p| * normalizedProjectiveProfileFirstMoment t := by
        rw [integral_const_mul]
        rfl
    _ =
      normalizedProjectiveProfileFirstMoment t * |q-p| := by ring

/--
Exact projective Abel variation bound on an increasing finite q-grid.
-/
theorem normalizedProjectiveBaseTransform_abelVariation_le
    {t Q : ℝ}
    (q : ℕ → ℝ) (n : ℕ)
    (hq0 : q 0 = 0)
    (hmono : ∀ i, i < n -> q i <= q (i+1))
    (hqQ : q n <= Q) :
    abelVariation
        (fun i => normalizedProjectiveBaseTransform t (q i)) n
      <=
    normalizedProjectiveProfileL1 t
      + normalizedProjectiveProfileFirstMoment t * Q := by
  have hend :=
    normalizedProjectiveBaseTransform_abs_le_profileL1 t (q n)
  have hsum :
      (∑ i ∈ Finset.range n,
        |normalizedProjectiveBaseTransform t (q i)
          - normalizedProjectiveBaseTransform t (q (i+1))|)
      <=
      normalizedProjectiveProfileFirstMoment t * (q n - q 0) := by
    calc
      (∑ i ∈ Finset.range n,
        |normalizedProjectiveBaseTransform t (q i)
          - normalizedProjectiveBaseTransform t (q (i+1))|)
      <=
      ∑ i ∈ Finset.range n,
        normalizedProjectiveProfileFirstMoment t
          * (q (i+1)-q i) := by
            apply Finset.sum_le_sum
            intro i hi
            have hi' := Finset.mem_range.mp hi
            have hqi := hmono i hi'
            have h :=
              normalizedProjectiveBaseTransform_lipschitz
                t (q (i+1)) (q i)
            rw [abs_sub_comm (q i) (q (i+1)),
                abs_of_nonneg (sub_nonneg.mpr hqi)] at h
            simpa [sub_eq_add_neg] using h
      _ =
      normalizedProjectiveProfileFirstMoment t * (q n - q 0) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub]
  unfold abelVariation
  rw [hq0] at hsum
  have hM1 := normalizedProjectiveProfileFirstMoment_nonneg t
  have hsumQ :
      (∑ i ∈ Finset.range n,
        |normalizedProjectiveBaseTransform t (q i)
          - normalizedProjectiveBaseTransform t (q (i+1))|)
      <= normalizedProjectiveProfileFirstMoment t * Q := by
    exact hsum.trans
      (mul_le_mul_of_nonneg_left hqQ hM1)
  linarith

end Synthesis
