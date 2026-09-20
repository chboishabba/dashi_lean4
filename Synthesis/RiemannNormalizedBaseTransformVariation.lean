import Synthesis.RiemannNormalizedHorizontalCorrectionBound
import Synthesis.RiemannNormalizedRvMRightDiscrepancy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Uniform mass, Lipschitz and Abel-variation bounds for the normalized base transform

The normalized centered profile

  H_t(v) = G_t(v) (cos(v/16)-1)

has a t-independent L1 bound because:
* each fixed symmetric affine bump has mass <= (pi/2) M0;
* 0 < lambda(t) <= quantitativeMixUpper for t>=18;
* |cos(v/16)-1| <= 2.

Hence

  integral |H_t| <= pi M0 (1+quantitativeMixUpper).

Its support satisfies |v| < 9*pi/4, so the first moment is bounded uniformly.
Using |cos x - cos y| <= |x-y| gives a uniform Lipschitz bound for

  Phi_t(q) = integral 4 H_t(v) cos(qv) dv.

Therefore on any increasing finite grid 0=q_0<=...<=q_n<=Q, the Abel variation

  |Phi_t(q_n)| + sum_{i<n}|Phi_t(q_i)-Phi_t(q_{i+1})|

is bounded by a constant depending only on Q and the fixed bump data, not on the
number of zero-count grid points.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace Synthesis

def normalizedCenteredMassUpper : ℝ :=
  Real.pi * unitBumpMass0 * (1 + quantitativeMixUpper)

def normalizedBaseTransformAbsUpper : ℝ :=
  4 * normalizedCenteredMassUpper

def normalizedBaseTransformLipschitzUpper : ℝ :=
  9 * Real.pi * normalizedCenteredMassUpper

theorem normalizedCenteredMassUpper_pos :
    0 < normalizedCenteredMassUpper := by
  unfold normalizedCenteredMassUpper
  have hm : 0 < unitBumpMass0 := unitBumpMass0_pos
  have hmix : 0 <= quantitativeMixUpper := by
    unfold quantitativeMixUpper
    positivity
  positivity

theorem normalizedBaseTransformAbsUpper_nonneg :
    0 <= normalizedBaseTransformAbsUpper :=
  (by unfold normalizedBaseTransformAbsUpper; positivity)

theorem normalizedBaseTransformLipschitzUpper_nonneg :
    0 <= normalizedBaseTransformLipschitzUpper :=
  (by unfold normalizedBaseTransformLipschitzUpper; positivity)

theorem normalizedInnerFixedProfile_mass_le :
    taperMass normalizedInnerFixedProfile
      <= (Real.pi / 2) * unitBumpMass0 := by
  rw [normalizedInnerFixedProfile_eq_symBump]
  have hR : 0 < Real.pi / 4 := by positivity
  have h :=
    taperMass_quantitativeSymBump_le
      (c := Real.pi) (R := Real.pi / 4) hR
  nlinarith

theorem normalizedOuterFixedProfile_mass_le :
    taperMass normalizedOuterFixedProfile
      <= (Real.pi / 2) * unitBumpMass0 := by
  rw [normalizedOuterFixedProfile_eq_symBump]
  have hR : 0 < Real.pi / 4 := by positivity
  have h :=
    taperMass_quantitativeSymBump_le
      (c := 2 * Real.pi) (R := Real.pi / 4) hR
  nlinarith

theorem normalizedCanonicalFixedProfile_mass_le
    {t : ℝ} (ht : 18 <= t) :
    taperMass (normalizedCanonicalFixedProfile t)
      <= (Real.pi / 2) * unitBumpMass0
          * (1 + quantitativeMixUpper) := by
  have hR : 0 < Real.pi / 4 := by positivity
  have hiC : Continuous normalizedInnerFixedProfile := by
    rw [normalizedInnerFixedProfile_eq_symBump]
    exact (quantitativeSymBump_contDiff hR.ne').continuous
  have hoC : Continuous normalizedOuterFixedProfile := by
    rw [normalizedOuterFixedProfile_eq_symBump]
    exact (quantitativeSymBump_contDiff hR.ne').continuous
  have hiK : HasCompactSupport normalizedInnerFixedProfile := by
    rw [normalizedInnerFixedProfile_eq_symBump]
    exact quantitativeSymBump_hasCompactSupport hR
  have hoK : HasCompactSupport normalizedOuterFixedProfile := by
    rw [normalizedOuterFixedProfile_eq_symBump]
    exact quantitativeSymBump_hasCompactSupport hR
  unfold normalizedCanonicalFixedProfile
  have hsum :=
    taperMass_add_smul_le
      hiC hiK hoC hoK (quantitativeLambda_pos ht).le
  have hi := normalizedInnerFixedProfile_mass_le
  have ho := normalizedOuterFixedProfile_mass_le
  have hlam := quantitativeLambda_le ht
  have hm0 : 0 <= unitBumpMass0 := unitBumpMass0_nonneg
  nlinarith [mul_nonneg hlam hm0]

theorem normalizedCenteredFixedProfile_mass_le
    {t : ℝ} (ht : 18 <= t) :
    (∫ v : ℝ, |normalizedCenteredFixedProfile t v|)
      <= normalizedCenteredMassUpper := by
  have hbaseC :=
    (normalizedCanonicalFixedProfile_contDiff t).continuous
  have hbaseK := normalizedCanonicalFixedProfile_compact t
  have hcenterC :=
    (normalizedCenteredFixedProfile_contDiff t).continuous
  have hcenterK := normalizedCenteredFixedProfile_compact t
  have hbaseAbs :
      Integrable (fun v : ℝ => |normalizedCanonicalFixedProfile t v|) :=
    hbaseC.abs.integrable_of_hasCompactSupport hbaseK.abs
  have hcenterAbs :
      Integrable (fun v : ℝ => |normalizedCenteredFixedProfile t v|) :=
    hcenterC.abs.integrable_of_hasCompactSupport hcenterK.abs
  have htwo :
      Integrable
        (fun v : ℝ => 2 * |normalizedCanonicalFixedProfile t v|) :=
    hbaseAbs.const_mul 2
  have hpoint : ∀ v : ℝ,
      |normalizedCenteredFixedProfile t v|
        <= 2 * |normalizedCanonicalFixedProfile t v| := by
    intro v
    unfold normalizedCenteredFixedProfile
    rw [abs_mul]
    have hcos :
        |Real.cos (v/16) - 1| <= 2 := by
      have h := Real.abs_cos_le_one (v/16)
      have htri := abs_sub (Real.cos (v/16)) 1
      norm_num at htri
      linarith
    exact mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
  have hint := integral_mono hcenterAbs htwo hpoint
  rw [integral_const_mul] at hint
  have hmass := normalizedCanonicalFixedProfile_mass_le ht
  unfold taperMass at hmass
  unfold normalizedCenteredMassUpper
  nlinarith

def normalizedCenteredFirstMoment (t : ℝ) : ℝ :=
  ∫ v : ℝ, |normalizedCenteredFixedProfile t v| * |v|

theorem normalizedCenteredFirstMoment_nonneg (t : ℝ) :
    0 <= normalizedCenteredFirstMoment t := by
  unfold normalizedCenteredFirstMoment
  positivity

theorem normalizedCenteredFirstMoment_le
    {t : ℝ} (ht : 18 <= t) :
    normalizedCenteredFirstMoment t
      <= (9 * Real.pi / 4) * normalizedCenteredMassUpper := by
  have hC := (normalizedCenteredFixedProfile_contDiff t).continuous
  have hK := normalizedCenteredFixedProfile_compact t
  have hleft :
      Integrable
        (fun v : ℝ =>
          |normalizedCenteredFixedProfile t v| * |v|) :=
    (hC.abs.mul continuous_abs).integrable_of_hasCompactSupport
      hK.abs.mul_right
  have hright :
      Integrable
        (fun v : ℝ =>
          (9 * Real.pi / 4)
            * |normalizedCenteredFixedProfile t v|) :=
    (hC.abs.integrable_of_hasCompactSupport hK.abs).const_mul _
  have hpoint : ∀ v : ℝ,
      |normalizedCenteredFixedProfile t v| * |v|
        <=
      (9 * Real.pi / 4)
        * |normalizedCenteredFixedProfile t v| := by
    intro v
    by_cases hv : normalizedCenteredFixedProfile t v = 0
    · simp [hv]
    · have hs := normalizedCenteredFixedProfile_support_upper hv
      have hnon := abs_nonneg (normalizedCenteredFixedProfile t v)
      nlinarith
  have hint := integral_mono hleft hright hpoint
  rw [integral_const_mul] at hint
  unfold normalizedCenteredFirstMoment
  exact le_trans hint
    (mul_le_mul_of_nonneg_left
      (normalizedCenteredFixedProfile_mass_le ht)
      (by positivity))

theorem normalizedCenteredBaseTransform_abs_le
    {t q : ℝ} (ht : 18 <= t) :
    |normalizedCenteredBaseTransform t q|
      <= normalizedBaseTransformAbsUpper := by
  unfold normalizedCenteredBaseTransform
  have hi := integrable_normalizedCenteredBase t q
  have habs :
      Integrable
        (fun v : ℝ => 4 * |normalizedCenteredFixedProfile t v|) := by
    exact ((normalizedCenteredFixedProfile_contDiff t).continuous.abs
      .integrable_of_hasCompactSupport
        (normalizedCenteredFixedProfile_compact t).abs).const_mul 4
  calc
    |∫ v : ℝ,
      4 * normalizedCenteredFixedProfile t v * Real.cos (q*v)|
      <=
    ∫ v : ℝ,
      |4 * normalizedCenteredFixedProfile t v * Real.cos (q*v)| :=
        abs_integral_le_integral_abs
    _ <=
    ∫ v : ℝ, 4 * |normalizedCenteredFixedProfile t v| := by
      apply integral_mono hi.abs habs
      intro v
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) <= 4)]
      have hc := Real.abs_cos_le_one (q*v)
      nlinarith [abs_nonneg (normalizedCenteredFixedProfile t v)]
    _ = 4 * ∫ v : ℝ, |normalizedCenteredFixedProfile t v| := by
      rw [integral_const_mul]
    _ <= normalizedBaseTransformAbsUpper := by
      unfold normalizedBaseTransformAbsUpper
      exact mul_le_mul_of_nonneg_left
        (normalizedCenteredFixedProfile_mass_le ht) (by norm_num)

theorem normalizedCenteredBaseTransform_lipschitz
    {t p q : ℝ} (ht : 18 <= t) :
    |normalizedCenteredBaseTransform t q
      - normalizedCenteredBaseTransform t p|
      <= normalizedBaseTransformLipschitzUpper * |q-p| := by
  unfold normalizedCenteredBaseTransform
  have hiq := integrable_normalizedCenteredBase t q
  have hip := integrable_normalizedCenteredBase t p
  rw [← integral_sub hiq hip]
  have hmomentC :
      Integrable
        (fun v : ℝ =>
          4 * |q-p|
            * (|normalizedCenteredFixedProfile t v| * |v|)) := by
    have hbase :
        Integrable
          (fun v : ℝ =>
            |normalizedCenteredFixedProfile t v| * |v|) :=
      ((normalizedCenteredFixedProfile_contDiff t).continuous.abs
        .mul continuous_abs).integrable_of_hasCompactSupport
          (normalizedCenteredFixedProfile_compact t).abs.mul_right
    exact hbase.const_mul (4 * |q-p|)
  calc
    |∫ v : ℝ,
      (4 * normalizedCenteredFixedProfile t v * Real.cos (q*v)
        - 4 * normalizedCenteredFixedProfile t v * Real.cos (p*v))|
      <=
    ∫ v : ℝ,
      |4 * normalizedCenteredFixedProfile t v * Real.cos (q*v)
        - 4 * normalizedCenteredFixedProfile t v * Real.cos (p*v)| :=
        abs_integral_le_integral_abs
    _ <=
    ∫ v : ℝ,
      4 * |q-p|
        * (|normalizedCenteredFixedProfile t v| * |v|) := by
      apply integral_mono (hiq.sub hip).abs hmomentC
      intro v
      have hc :=
        Real.abs_cos_sub_cos_le (q*v) (p*v)
      have hfactor :
          |q*v - p*v| = |q-p| * |v| := by
        rw [← sub_mul, abs_mul]
      calc
        |4 * normalizedCenteredFixedProfile t v * Real.cos (q*v)
          - 4 * normalizedCenteredFixedProfile t v * Real.cos (p*v)|
          =
        4 * |normalizedCenteredFixedProfile t v|
          * |Real.cos (q*v) - Real.cos (p*v)| := by
            rw [← mul_sub, abs_mul, abs_mul,
              abs_of_nonneg (by norm_num : (0:ℝ) <= 4)]
        _ <=
        4 * |normalizedCenteredFixedProfile t v| * |q*v-p*v| := by
          gcongr
        _ =
        4 * |q-p|
          * (|normalizedCenteredFixedProfile t v| * |v|) := by
          rw [hfactor]
          ring
    _ =
      4 * |q-p| * normalizedCenteredFirstMoment t := by
        rw [integral_const_mul]
        rfl
    _ <= normalizedBaseTransformLipschitzUpper * |q-p| := by
      have hm := normalizedCenteredFirstMoment_le ht
      unfold normalizedBaseTransformLipschitzUpper
      have habs : 0 <= |q-p| := abs_nonneg _
      nlinarith

/--
Uniform finite Abel variation on an increasing normalized right-gap grid.
-/
theorem normalizedBaseTransform_abelVariation_le
    {t Q : ℝ} (ht : 18 <= t)
    (q : ℕ → ℝ) (n : ℕ)
    (hq0 : q 0 = 0)
    (hmono : ∀ i, i < n -> q i <= q (i+1))
    (hqQ : q n <= Q) :
    abelVariation
        (fun i => normalizedCenteredBaseTransform t (q i)) n
      <=
    normalizedBaseTransformAbsUpper
      + normalizedBaseTransformLipschitzUpper * Q := by
  have hend :=
    normalizedCenteredBaseTransform_abs_le
      (t := t) (q := q n) ht
  have hsum :
      (∑ i ∈ Finset.range n,
        |normalizedCenteredBaseTransform t (q i)
          - normalizedCenteredBaseTransform t (q (i+1))|)
      <=
      normalizedBaseTransformLipschitzUpper
        * (q n - q 0) := by
    have hterm : ∀ i ∈ Finset.range n,
        |normalizedCenteredBaseTransform t (q i)
          - normalizedCenteredBaseTransform t (q (i+1))|
        <=
        normalizedBaseTransformLipschitzUpper
          * (q (i+1)-q i) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hqi := hmono i hi'
      have h :=
        normalizedCenteredBaseTransform_lipschitz
          (t := t) (p := q (i+1)) (q := q i) ht
      rw [abs_sub_comm (q i) (q (i+1)),
          abs_of_nonneg (sub_nonneg.mpr hqi)] at h
      simpa [sub_eq_add_neg] using h
    calc
      (∑ i ∈ Finset.range n,
        |normalizedCenteredBaseTransform t (q i)
          - normalizedCenteredBaseTransform t (q (i+1))|)
        <=
      ∑ i ∈ Finset.range n,
        normalizedBaseTransformLipschitzUpper
          * (q (i+1)-q i) :=
        Finset.sum_le_sum hterm
      _ =
      normalizedBaseTransformLipschitzUpper
        * (q n - q 0) := by
          rw [← Finset.mul_sum, Finset.sum_range_sub]
  unfold abelVariation
  rw [hq0] at hsum
  have hsumQ :
      (∑ i ∈ Finset.range n,
        |normalizedCenteredBaseTransform t (q i)
          - normalizedCenteredBaseTransform t (q (i+1))|)
      <= normalizedBaseTransformLipschitzUpper * Q := by
    exact le_trans hsum
      (mul_le_mul_of_nonneg_left hqQ
        normalizedBaseTransformLipschitzUpper_nonneg)
  linarith

end Synthesis
