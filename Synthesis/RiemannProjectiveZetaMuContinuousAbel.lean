import Synthesis.RiemannZetaMuExactAbel
import Synthesis.RiemannNormalizedProjectiveBaseTransformDerivativeRegularity
import Synthesis.RiemannZeta23RvMArbitraryEndpointDiscrepancy

/-!
# Continuous literal N-mu Abel theorem for the projective base consumer

This removes the last finite-grid surrogate from the projective q-only lane.

For the physical ordinate test

  phi_t(gamma) = Phi_proj(t,(gamma-t)/t),

the literal zero pairing minus the theorem-bearing RvM mu pairing satisfies

  Z_phi(A,B) - integral_A^B phi_t mu
    =
  phi_t(B) D_A(B)
    - integral_A^B phi_t'(x) D_A(x) dx,

where

  D_A(x) = Ncount(A,x) - integral_A^x mu.

The existing arbitrary-endpoint Zeta23 theorem bounds D_A(x) by O(log A+log x).
Combining it with the projective profile L1 and first moment gives a direct
continuous bound for the exact same-object projective discrepancy consumer.

No smooth surrogate density, q-grid, quadrature, or missing-tail decomposition
appears.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval Real

namespace Synthesis

def projectiveZetaMuWindowResidual
    (t A B : ℝ) : ℝ :=
  zetaWindowMinusMuPair A B (normalizedProjectiveOrdinateTest t)

theorem projectiveZetaMuWindowResidual_eq_discrepancyAbel
    {t A B : ℝ}
    (ht : t ≠ 0)
    (hAB : A ≤ B) :
    projectiveZetaMuWindowResidual t A B
      =
    normalizedProjectiveOrdinateTest t B
        * zetaMuCumulativeDiscrepancy A B
      -
    ∫ x in A..B,
      normalizedProjectiveOrdinateTestDeriv t x
        * zetaMuCumulativeDiscrepancy A x := by
  unfold projectiveZetaMuWindowResidual
  exact zetaWindowMinusMuPair_eq_discrepancyAbel
    (A := A) (B := B)
    (phi := normalizedProjectiveOrdinateTest t)
    (phi' := normalizedProjectiveOrdinateTestDeriv t)
    hAB
    (by
      intro x hx
      exact normalizedProjectiveOrdinateTest_hasDerivAt ht)
    (normalizedProjectiveOrdinateTestDeriv_intervalIntegrable ht)

theorem normalizedProjectiveOrdinateTest_abs_le_profileL1
    (t gamma : ℝ) :
    |normalizedProjectiveOrdinateTest t gamma|
      ≤ normalizedProjectiveProfileL1 t := by
  unfold normalizedProjectiveOrdinateTest
  exact normalizedProjectiveBaseTransform_abs_le_profileL1
    t ((gamma - t) / t)

/--
Quantitative continuous projective N-mu discrepancy bound on every high finite
ordinate window.

The constant C and threshold T0 are exactly those supplied by the literal
Zeta23 arbitrary-endpoint discrepancy theorem.  The profile factors are the
actual projective L1 mass and first moment.
-/
theorem exists_projectiveZetaMuWindowResidual_bound :
    ∃ C T0 : ℝ, 0 ≤ C ∧
      ∀ t A B : ℝ,
        0 < t ->
        max T0 4 ≤ A ->
        A < B ->
        |projectiveZetaMuWindowResidual t A B|
          ≤
        (C * (Real.log (A + 3) + Real.log (B + 4)))
          *
        (normalizedProjectiveProfileL1 t
          + ((B - A) / t)
            * normalizedProjectiveProfileFirstMoment t) := by
  obtain ⟨C, T0, hC, hD⟩ :=
    exists_zetaMuWindowDiscrepancy_arbitrary_bound
  refine ⟨C, T0, hC, ?_⟩
  intro t A B ht hA hAB
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hABle : A ≤ B := hAB.le
  let Dmax : ℝ :=
    C * (Real.log (A + 3) + Real.log (B + 4))
  have hlogA : 0 ≤ Real.log (A + 3) := by
    apply Real.log_nonneg
    have hA4 : 4 ≤ A := (le_max_right T0 4).trans hA
    linarith
  have hlogB : 0 ≤ Real.log (B + 4) := by
    apply Real.log_nonneg
    have hA4 : 4 ≤ A := (le_max_right T0 4).trans hA
    linarith
  have hDmax : 0 ≤ Dmax := by
    dsimp [Dmax]
    positivity

  have hdiscB :
      |zetaMuCumulativeDiscrepancy A B| ≤ Dmax := by
    rw [zetaMuCumulativeDiscrepancy_endpoint]
    simpa [Dmax] using hD A B hA hAB

  have hdisc :
      ∀ x ∈ Set.uIoc A B,
        |zetaMuCumulativeDiscrepancy A x| ≤ Dmax := by
    intro x hx
    rw [Set.uIoc_of_le hABle] at hx
    have hraw := hD A x hA hx.1
    rw [zetaMuCumulativeDiscrepancy_endpoint]
    have hxpos : 0 < x + 4 := by
      have hA4 : 4 ≤ A := (le_max_right T0 4).trans hA
      linarith
    have hlogle :
        Real.log (x + 4) ≤ Real.log (B + 4) :=
      Real.log_le_log hxpos (by linarith)
    exact hraw.trans (by
      dsimp [Dmax]
      have hadd :
          Real.log (A + 3) + Real.log (x + 4)
            ≤
          Real.log (A + 3) + Real.log (B + 4) :=
        add_le_add_left hlogle _
      exact mul_le_mul_of_nonneg_left hadd hC)

  have htailPoint :
      ∀ x ∈ Set.uIoc A B,
        |normalizedProjectiveOrdinateTestDeriv t x
          * zetaMuCumulativeDiscrepancy A x|
          ≤
        ((1 / t) * normalizedProjectiveProfileFirstMoment t) * Dmax := by
    intro x hx
    rw [abs_mul]
    exact mul_le_mul
      (normalizedProjectiveOrdinateTestDeriv_abs_le ht)
      (hdisc x hx)
      (abs_nonneg _)
      (by positivity)

  have htailRaw :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun x =>
        normalizedProjectiveOrdinateTestDeriv t x
          * zetaMuCumulativeDiscrepancy A x)
      htailPoint
  have htail :
      |∫ x in A..B,
        normalizedProjectiveOrdinateTestDeriv t x
          * zetaMuCumulativeDiscrepancy A x|
        ≤
      (((1 / t) * normalizedProjectiveProfileFirstMoment t) * Dmax)
        * (B - A) := by
    rw [Real.norm_eq_abs] at htailRaw
    rw [abs_of_nonneg (sub_nonneg.mpr hABle)] at htailRaw
    exact htailRaw

  have hend :
      |normalizedProjectiveOrdinateTest t B
        * zetaMuCumulativeDiscrepancy A B|
        ≤
      normalizedProjectiveProfileL1 t * Dmax := by
    rw [abs_mul]
    exact mul_le_mul
      (normalizedProjectiveOrdinateTest_abs_le_profileL1 t B)
      hdiscB
      (abs_nonneg _)
      (normalizedProjectiveProfileL1_nonneg t)

  rw [projectiveZetaMuWindowResidual_eq_discrepancyAbel ht hABle]
  calc
    |normalizedProjectiveOrdinateTest t B
        * zetaMuCumulativeDiscrepancy A B
      -
      ∫ x in A..B,
        normalizedProjectiveOrdinateTestDeriv t x
          * zetaMuCumulativeDiscrepancy A x|
      ≤
    |normalizedProjectiveOrdinateTest t B
        * zetaMuCumulativeDiscrepancy A B|
      +
    |∫ x in A..B,
        normalizedProjectiveOrdinateTestDeriv t x
          * zetaMuCumulativeDiscrepancy A x| :=
      abs_sub _ _
    _ ≤
      normalizedProjectiveProfileL1 t * Dmax
        +
      (((1 / t) * normalizedProjectiveProfileFirstMoment t) * Dmax)
        * (B - A) := add_le_add hend htail
    _ =
      Dmax *
        (normalizedProjectiveProfileL1 t
          + ((B - A) / t)
            * normalizedProjectiveProfileFirstMoment t) := by
      field_simp [ht0]
      ring
    _ =
      (C * (Real.log (A + 3) + Real.log (B + 4)))
        *
      (normalizedProjectiveProfileL1 t
        + ((B - A) / t)
          * normalizedProjectiveProfileFirstMoment t) := rfl

end Synthesis
