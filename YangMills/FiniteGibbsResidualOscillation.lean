import Mathlib
import YangMills.FiniteGibbsResidualComparison

/-!
# Complete/Wilson Gibbs transfer controlled by residual oscillation

The absolute magnitude of the selected residual
  R = E + R_operation + Boundary + Vacuum
is not the natural quantity for NORMALIZED Gibbs expectations.
If
  lower ≤ R(U) ≤ upper
for every finite link field U, then

  E_full[F] ≤ exp(upper-lower) E_Wilson[F],   F ≥ 0.

Thus adding an arbitrary configuration-independent vacuum constant to R
does not change the comparison factor.  This is strictly sharper than
centering first and using exp(2K): it records the exact oscillation width
upper-lower directly.

The theorem remains finite-cutoff.  A Clay-facing continuum transfer
requires the selected CMP119 source to prove a scale-compatible bound
on this oscillation, or a stronger direct observable estimate.
-/

namespace RequestProject.YangMills

/--
Two different constants may pay the Gibbs numerator and partition
comparison. Their product, not the square of either one, is the
normalized expectation loss.
-/
theorem nonnegative_gibbs_ratio_comparison_two_constants
    (A B Nfull Nwilson Zfull Zwilson : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hNwilson : 0 ≤ Nwilson)
    (hZfull : 0 < Zfull)
    (hZwilson : 0 < Zwilson)
    (hNumerator : Nfull ≤ A * Nwilson)
    (hPartition : Zwilson ≤ B * Zfull) :
    Nfull / Zfull ≤
      (A * B) * (Nwilson / Zwilson) := by
  have h1 :
      Nfull * Zwilson ≤
        A * Nwilson * Zwilson :=
    mul_le_mul_of_nonneg_right hNumerator hZwilson.le
  have h2 :
      A * Nwilson * Zwilson ≤
        A * Nwilson * (B * Zfull) :=
    mul_le_mul_of_nonneg_left hPartition
      (mul_nonneg hA hNwilson)
  apply (div_le_div_iff₀ hZfull hZwilson).2
  calc
    Nfull * Zwilson ≤
        A * Nwilson * Zwilson := h1
    _ ≤ A * Nwilson * (B * Zfull) := h2
    _ = ((A * B) * (Nwilson / Zwilson)) *
          (Zfull * Zwilson) := by
        field_simp [ne_of_gt hZwilson]
        ring

/--
Exact pointwise full/Wilson density comparison from asymmetric
residual lower and upper bounds.
-/
theorem su2_complete_weight_two_sided_of_residual_interval
    (L : ℕ) [NeZero L] (β lower upper : ℝ)
    (regular rOperation boundary vacuum : SU2TorusLinks L → ℝ)
    (hResidual : ∀ links,
      lower ≤ su2FullResidual
        regular rOperation boundary vacuum links ∧
      su2FullResidual
        regular rOperation boundary vacuum links ≤ upper)
    (links : SU2TorusLinks L) :
    Real.exp (-upper) * su2PhysicalWilsonWeight L β links ≤
      su2FourDimensionalCompleteWeight L links β
        regular rOperation boundary vacuum ∧
    su2FourDimensionalCompleteWeight L links β
        regular rOperation boundary vacuum ≤
      Real.exp (-lower) * su2PhysicalWilsonWeight L β links := by
  rw [su2_complete_weight_factorizes_exactly]
  have hWilson : 0 ≤ su2PhysicalWilsonWeight L β links :=
    (Real.exp_pos _).le
  constructor
  · calc
      Real.exp (-upper) * su2PhysicalWilsonWeight L β links ≤
        Real.exp (-(su2FullResidual
          regular rOperation boundary vacuum links)) *
          su2PhysicalWilsonWeight L β links :=
            mul_le_mul_of_nonneg_right
              (Real.exp_le_exp.mpr
                (neg_le_neg (hResidual links).2)) hWilson
      _ = _ := by ring
  · calc
      su2PhysicalWilsonWeight L β links *
          Real.exp (-(su2FullResidual
            regular rOperation boundary vacuum links)) ≤
        su2PhysicalWilsonWeight L β links *
          Real.exp (-lower) :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr
                (neg_le_neg (hResidual links).1)) hWilson
      _ = _ := by ring

/--
SHARP finite normalized positive-observable comparison by the
residual oscillation width upper-lower.
-/
theorem su2_complete_normalized_vs_wilson_expectation_of_residual_interval
    (L : ℕ) [NeZero L]
    (haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L))
    (β lower upper : ℝ)
    (regular rOperation boundary vacuum : SU2TorusLinks L → ℝ)
    (hResidual : ∀ links,
      lower ≤ su2FullResidual
        regular rOperation boundary vacuum links ∧
      su2FullResidual
        regular rOperation boundary vacuum links ≤ upper)
    (probe : SU2TorusLinks L → ℝ)
    (hProbe : ∀ links, 0 ≤ probe links)
    (hIntegrableFull :
      MeasureTheory.Integrable
        (su2FourDimensionalCompleteWeight L · β
          regular rOperation boundary vacuum)
        ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L)))
    (hIntegrableWilson :
      MeasureTheory.Integrable
        (su2PhysicalWilsonWeight L β)
        ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L)))
    (hIntegrableFullProbe :
      MeasureTheory.Integrable
        (fun links =>
          su2FourDimensionalCompleteWeight L links β
            regular rOperation boundary vacuum * probe links)
        ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L)))
    (hIntegrableWilsonProbe :
      MeasureTheory.Integrable
        (fun links =>
          su2PhysicalWilsonWeight L β links * probe links)
        ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L)))
    (hZFull : 0 <
      ∫ links : SU2TorusLinks L,
        su2FourDimensionalCompleteWeight L links β
          regular rOperation boundary vacuum
        ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L)))
    (hZWilson : 0 <
      ∫ links : SU2TorusLinks L,
        su2PhysicalWilsonWeight L β links
        ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L))) :
    (∫ links : SU2TorusLinks L,
        su2FourDimensionalCompleteWeight L links β
          regular rOperation boundary vacuum * probe links
        ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L))) /
      (∫ links : SU2TorusLinks L,
        su2FourDimensionalCompleteWeight L links β
          regular rOperation boundary vacuum
        ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L))) ≤
    Real.exp (upper - lower) *
      ((∫ links : SU2TorusLinks L,
          su2PhysicalWilsonWeight L β links * probe links
          ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
            MeasureTheory.Measure (SU2TorusLinks L))) /
        (∫ links : SU2TorusLinks L,
          su2PhysicalWilsonWeight L β links
          ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
            MeasureTheory.Measure (SU2TorusLinks L)))) := by
  let μ : MeasureTheory.Measure (SU2TorusLinks L) := haar
  let w0 : SU2TorusLinks L → ℝ := su2PhysicalWilsonWeight L β
  let w : SU2TorusLinks L → ℝ :=
    fun x => su2FourDimensionalCompleteWeight L x β
      regular rOperation boundary vacuum
  let A := Real.exp (-lower)
  let B := Real.exp upper
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hB : 0 ≤ B := (Real.exp_pos _).le
  have hnum :
      (∫ x : SU2TorusLinks L, w x * probe x ∂μ) ≤
      A * (∫ x : SU2TorusLinks L, w0 x * probe x ∂μ) := by
    calc
      _ ≤ ∫ x : SU2TorusLinks L,
          A * (w0 x * probe x) ∂μ := by
        apply MeasureTheory.integral_mono
          hIntegrableFullProbe
          (hIntegrableWilsonProbe.const_mul A)
        intro x
        have h :=
          (su2_complete_weight_two_sided_of_residual_interval
            L β lower upper regular rOperation boundary vacuum
            hResidual x).2
        change w x ≤ A * w0 x at h
        calc
          w x * probe x ≤ (A * w0 x) * probe x :=
            mul_le_mul_of_nonneg_right h (hProbe x)
          _ = A * (w0 x * probe x) := by ring
      _ = _ := by rw [MeasureTheory.integral_const_mul]
  have hzlower :
      Real.exp (-upper) *
          (∫ x : SU2TorusLinks L, w0 x ∂μ) ≤
      ∫ x : SU2TorusLinks L, w x ∂μ := by
    calc
      _ = ∫ x : SU2TorusLinks L,
          Real.exp (-upper) * w0 x ∂μ := by
            rw [MeasureTheory.integral_const_mul]
      _ ≤ _ := by
        apply MeasureTheory.integral_mono
          (hIntegrableWilson.const_mul (Real.exp (-upper)))
          hIntegrableFull
        intro x
        exact
          (su2_complete_weight_two_sided_of_residual_interval
            L β lower upper regular rOperation boundary vacuum
            hResidual x).1
  have hZcomp :
      (∫ x : SU2TorusLinks L, w0 x ∂μ) ≤
      B * (∫ x : SU2TorusLinks L, w x ∂μ) := by
    have hcancel :
        B * Real.exp (-upper) = 1 := by
      dsimp [B]
      rw [← Real.exp_add]
      simp
    calc
      _ = B * (Real.exp (-upper) *
          (∫ x : SU2TorusLinks L, w0 x ∂μ)) := by
            rw [← mul_assoc, hcancel, one_mul]
      _ ≤ B * (∫ x : SU2TorusLinks L, w x ∂μ) :=
        mul_le_mul_of_nonneg_left hzlower hB
  have hnwilson : 0 ≤
      ∫ x : SU2TorusLinks L, w0 x * probe x ∂μ := by
    apply MeasureTheory.integral_nonneg
    intro x
    exact mul_nonneg (Real.exp_pos _).le (hProbe x)
  have hq := nonnegative_gibbs_ratio_comparison_two_constants
    A B
    (∫ x : SU2TorusLinks L, w x * probe x ∂μ)
    (∫ x : SU2TorusLinks L, w0 x * probe x ∂μ)
    (∫ x : SU2TorusLinks L, w x ∂μ)
    (∫ x : SU2TorusLinks L, w0 x ∂μ)
    hA hB hnwilson hZFull hZWilson hnum hZcomp
  have hCoefficient :
      A * B = Real.exp (upper - lower) := by
    dsimp [A, B]
    rw [← Real.exp_add]
    congr 1
    ring
  simpa only [hCoefficient] using hq

/--
An additive constant shift of the entire selected residual leaves its
oscillation width exactly unchanged.
-/
theorem residual_interval_shift_invariant
    {L : ℕ}
    (regular rOperation boundary vacuum : SU2TorusLinks L → ℝ)
    (lower upper shift : ℝ)
    (hResidual : ∀ links,
      lower ≤ su2FullResidual regular rOperation boundary vacuum links ∧
      su2FullResidual regular rOperation boundary vacuum links ≤ upper) :
    ∀ links,
      lower + shift ≤
        su2FullResidual regular rOperation boundary
          (fun x => vacuum x + shift) links ∧
      su2FullResidual regular rOperation boundary
          (fun x => vacuum x + shift) links ≤ upper + shift := by
  intro links
  dsimp [su2FullResidual]
  constructor <;> linarith [(hResidual links).1, (hResidual links).2]

end RequestProject.YangMills
