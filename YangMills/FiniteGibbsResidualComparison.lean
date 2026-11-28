import Mathlib
import YangMills.LiteralSU2FourDimensionalLattice
import YangMills.LiteralSU2NativeGibbsProbability

/-!
# Quantitative finite Gibbs comparison retaining ALL CMP119 residual sectors

Let W be the actual link-derived Wilson action and
R = E + R_operation + B + Vacuum the complete extra effective action.
The ratio of full and Wilson-only Boltzmann weights is EXACTLY exp(-R).

If the *total* residual oscillation around a constant is controlled
between -K and K, then the full Gibbs partition and positive cylinder
numerators are controlled by e^K times the Wilson ones, and the
NORMALIZED expectations have e^(2K) comparison. A constant vacuum
term can be subtracted before estimating the oscillation, because it
cancels identically in normalized Gibbs expectations.

These are finite-source estimates, not claims that CMP119 supplies a
cutoff-independent K. If K grows with cutoff the comparison is
insufficient for UV tightness; if the Wilson baseline fails to have
scale-sensitive moments, this comparison alone cannot create them.

Reflection positivity is a separate issue: bounds on |R| do not
preserve OS2; see FiniteReflectionKernelAudit.
-/

namespace RequestProject.YangMills

/-- All four non-Wilson sectors remain explicit on the lattice carrier. -/
def su2FullResidual
    {L : ℕ}
    (regular rOperation boundary vacuum : SU2TorusLinks L → ℝ)
    (links : SU2TorusLinks L) : ℝ :=
  regular links + rOperation links + boundary links + vacuum links

/-- Wilson-only physical lattice density. -/
def su2PhysicalWilsonWeight
    (L : ℕ) [NeZero L] (β : ℝ) (links : SU2TorusLinks L) : ℝ :=
  Real.exp (-(su2FourDimensionalWilsonAction L links β))

/-- Full physical density equals the Wilson density times one residual. -/
theorem su2_complete_weight_factorizes_exactly
    (L : ℕ) [NeZero L] (β : ℝ)
    (regular rOperation boundary vacuum : SU2TorusLinks L → ℝ)
    (links : SU2TorusLinks L) :
    su2FourDimensionalCompleteWeight L links β
      regular rOperation boundary vacuum =
      su2PhysicalWilsonWeight L β links *
        Real.exp (-(su2FullResidual
          regular rOperation boundary vacuum links)) := by
  unfold su2FourDimensionalCompleteWeight
    su2FourDimensionalCompleteAction su2PhysicalWilsonWeight
    su2FullResidual
  rw [show
      -(su2FourDimensionalWilsonAction L links β +
        regular links + rOperation links + boundary links + vacuum links) =
      -(su2FourDimensionalWilsonAction L links β) -
        (regular links + rOperation links +
          boundary links + vacuum links) by ring]
  rw [sub_eq_add_neg, Real.exp_add]

/--
Complete-vs-Wilson pointwise quantitative comparison.
No "perturbatively small" assertion: the dependence exp(K) is exact,
and K includes every source effective-action sector.
-/
theorem su2_complete_weight_two_sided_of_residual_bound
    (L : ℕ) [NeZero L] (β : ℝ)
    (regular rOperation boundary vacuum : SU2TorusLinks L → ℝ)
    (K : ℝ)
    (hResidual :
      ∀ links, -K ≤ su2FullResidual
        regular rOperation boundary vacuum links ∧
        su2FullResidual
          regular rOperation boundary vacuum links ≤ K)
    (links : SU2TorusLinks L) :
    Real.exp (-K) * su2PhysicalWilsonWeight L β links ≤
      su2FourDimensionalCompleteWeight L links β
        regular rOperation boundary vacuum ∧
    su2FourDimensionalCompleteWeight L links β
        regular rOperation boundary vacuum ≤
      Real.exp K * su2PhysicalWilsonWeight L β links := by
  rw [su2_complete_weight_factorizes_exactly]
  have hWilson : 0 ≤ su2PhysicalWilsonWeight L β links :=
    (Real.exp_pos _).le
  constructor
  · calc
      Real.exp (-K) * su2PhysicalWilsonWeight L β links ≤
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
        su2PhysicalWilsonWeight L β links * Real.exp K :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr
                (neg_le_neg (hResidual links).1)) hWilson
      _ = _ := by ring

/--
A fixed additive vacuum normalization cancels from EVERY finite
normalized Gibbs expectation. Thus only residual oscillation matters.
-/
theorem su2_shift_complete_action_by_constant
    (L : ℕ) [NeZero L] (β : ℝ)
    (regular rOperation boundary vacuum : SU2TorusLinks L → ℝ)
    (shift : ℝ) (links : SU2TorusLinks L) :
    su2FourDimensionalCompleteWeight L links β
      regular rOperation boundary (fun x => vacuum x + shift) =
    Real.exp (-shift) *
      su2FourDimensionalCompleteWeight L links β
        regular rOperation boundary vacuum := by
  unfold su2FourDimensionalCompleteWeight
    su2FourDimensionalCompleteAction
  rw [show
      -(su2FourDimensionalWilsonAction L links β +
        regular links + rOperation links + boundary links +
        (vacuum links + shift)) =
      -shift -
        (su2FourDimensionalWilsonAction L links β +
          regular links + rOperation links + boundary links +
          vacuum links) by ring]
  rw [sub_eq_add_neg, Real.exp_add]

/-- Explicit bounded-observable normalization with a complete physical density. -/
theorem su2_complete_normalized_expectation_of_bounded_probe
    (L : ℕ) [NeZero L]
    (haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L))
    (β : ℝ)
    (regular rOperation boundary vacuum : SU2TorusLinks L → ℝ)
    (probe : SU2TorusLinks L → ℝ) (M : ℝ)
    (hProbe : ∀ links, 0 ≤ probe links ∧ probe links ≤ M)
    (hZ : 0 <
      ∫ links : SU2TorusLinks L,
        su2FourDimensionalCompleteWeight L links β
          regular rOperation boundary vacuum
      ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
        MeasureTheory.Measure (SU2TorusLinks L)))
    (hWeightIntegrable :
      MeasureTheory.Integrable
        (su2FourDimensionalCompleteWeight L · β
          regular rOperation boundary vacuum)
        ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L)))
    (hProbeIntegrable :
      MeasureTheory.Integrable
        (fun links : SU2TorusLinks L =>
          su2FourDimensionalCompleteWeight L links β
            regular rOperation boundary vacuum * probe links)
        ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
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
        MeasureTheory.Measure (SU2TorusLinks L)))
    ≤ M := by
  have hMajorant :
      ∫ links : SU2TorusLinks L,
        su2FourDimensionalCompleteWeight L links β
          regular rOperation boundary vacuum * probe links
      ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
        MeasureTheory.Measure (SU2TorusLinks L)) ≤
      M *
        (∫ links : SU2TorusLinks L,
          su2FourDimensionalCompleteWeight L links β
            regular rOperation boundary vacuum
        ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L))) := by
    calc
      _ ≤ ∫ links : SU2TorusLinks L,
          M * su2FourDimensionalCompleteWeight L links β
            regular rOperation boundary vacuum
          ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
            MeasureTheory.Measure (SU2TorusLinks L)) := by
              apply MeasureTheory.integral_mono
                hProbeIntegrable (hWeightIntegrable.const_mul M)
              intro links
              have hw := (su2_four_dimensional_complete_weight_positive
                L links β regular rOperation boundary vacuum).le
              calc
                _ ≤ su2FourDimensionalCompleteWeight L links β
                      regular rOperation boundary vacuum * M :=
                    mul_le_mul_of_nonneg_left (hProbe links).2 hw
                _ = _ := mul_comm _ _
      _ = _ := by rw [MeasureTheory.integral_const_mul]
  exact (div_le_iff₀ hZ).mpr hMajorant

/--
Pure real division lemma showing the exact loss from comparing two
normalized positive finite measures. The denominator comparison
must be used as well as the numerator comparison: one cannot obtain
the sharp e^(2K) factor by comparing Gibbs numerators alone.
-/
theorem nonnegative_gibbs_ratio_comparison
    (C Nfull Nwilson Zfull Zwilson : ℝ)
    (hC : 0 ≤ C)
    (hNwilson : 0 ≤ Nwilson)
    (hZfull : 0 < Zfull)
    (hZwilson : 0 < Zwilson)
    (hNumerator : Nfull ≤ C * Nwilson)
    (hPartition : Zwilson ≤ C * Zfull) :
    Nfull / Zfull ≤ C ^ 2 * (Nwilson / Zwilson) := by
  have hA :
      Nfull * Zwilson ≤ C * Nwilson * Zwilson :=
    mul_le_mul_of_nonneg_right hNumerator hZwilson.le
  have hB :
      C * Nwilson * Zwilson ≤
        C * Nwilson * (C * Zfull) :=
    mul_le_mul_of_nonneg_left hPartition
      (mul_nonneg hC hNwilson)
  calc
    Nfull / Zfull ≤ (C ^ 2 * Nwilson) / Zwilson := by
      apply (div_le_div_iff₀ hZfull hZwilson).2
      calc
        Nfull * Zwilson ≤ C * Nwilson * Zwilson := hA
        _ ≤ C * Nwilson * (C * Zfull) := hB
        _ = (C ^ 2 * Nwilson) * Zfull := by ring
    _ = C ^ 2 * (Nwilson / Zwilson) := by ring

/--
NONTRIVIAL quantitative transfer from the complete physical five-sector
finite SU(2) Gibbs law to the Wilson-only law.  Every finite positive
cylinder probe enjoys an explicit comparison by exp(2K), where
-K ≤ E+R+B+Vacuum ≤ K on the literal LINK configuration carrier.

This establishes a rigorous route for importing an existing Wilson
continuum bound if, and only if, the selected CMP119 RG construction
produces a K controlled uniformly along the cutoff trajectory.
It does not infer such a K from bounded SU(2) plaquette costs.
-/
theorem su2_complete_normalized_vs_wilson_expectation
    (L : ℕ) [NeZero L]
    (haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L))
    (β : ℝ)
    (regular rOperation boundary vacuum : SU2TorusLinks L → ℝ)
    (K : ℝ)
    (hResidual : ∀ links,
      -K ≤ su2FullResidual regular rOperation boundary vacuum links ∧
      su2FullResidual regular rOperation boundary vacuum links ≤ K)
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
    Real.exp (2 * K) *
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
  let C := Real.exp K
  let D := Real.exp (-K)
  have hC : 0 ≤ C := (Real.exp_pos _).le
  have hCD : C * D = 1 := by
    dsimp [C, D]
    rw [← Real.exp_add]
    simp
  have hnum :
      (∫ x : SU2TorusLinks L, w x * probe x ∂μ) ≤
      C * (∫ x : SU2TorusLinks L, w0 x * probe x ∂μ) := by
    calc
      _ ≤ ∫ x : SU2TorusLinks L,
          C * (w0 x * probe x) ∂μ := by
        apply MeasureTheory.integral_mono
          hIntegrableFullProbe
          (hIntegrableWilsonProbe.const_mul C)
        intro x
        have h := (su2_complete_weight_two_sided_of_residual_bound
          L β regular rOperation boundary vacuum K hResidual x).2
        change w x ≤ C * w0 x at h
        calc
          w x * probe x ≤ (C * w0 x) * probe x :=
            mul_le_mul_of_nonneg_right h (hProbe x)
          _ = C * (w0 x * probe x) := by ring
      _ = _ := by rw [MeasureTheory.integral_const_mul]
  have hzlower :
      D * (∫ x : SU2TorusLinks L, w0 x ∂μ) ≤
      ∫ x : SU2TorusLinks L, w x ∂μ := by
    calc
      _ = ∫ x : SU2TorusLinks L, D * w0 x ∂μ := by
        rw [MeasureTheory.integral_const_mul]
      _ ≤ _ := by
        apply MeasureTheory.integral_mono
          (hIntegrableWilson.const_mul D) hIntegrableFull
        intro x
        exact (su2_complete_weight_two_sided_of_residual_bound
          L β regular rOperation boundary vacuum K hResidual x).1
  have hZcomp :
      (∫ x : SU2TorusLinks L, w0 x ∂μ) ≤
      C * (∫ x : SU2TorusLinks L, w x ∂μ) := by
    calc
      _ = C * (D * (∫ x : SU2TorusLinks L, w0 x ∂μ)) := by
        rw [← mul_assoc, hCD, one_mul]
      _ ≤ C * (∫ x : SU2TorusLinks L, w x ∂μ) :=
        mul_le_mul_of_nonneg_left hzlower hC
  have hnwilson : 0 ≤
      ∫ x : SU2TorusLinks L, w0 x * probe x ∂μ := by
    apply MeasureTheory.integral_nonneg
    intro x
    exact mul_nonneg (Real.exp_pos _).le (hProbe x)
  have hq := nonnegative_gibbs_ratio_comparison
    C
    (∫ x : SU2TorusLinks L, w x * probe x ∂μ)
    (∫ x : SU2TorusLinks L, w0 x * probe x ∂μ)
    (∫ x : SU2TorusLinks L, w x ∂μ)
    (∫ x : SU2TorusLinks L, w0 x ∂μ)
    hC hnwilson hZFull hZWilson hnum hZcomp
  have hCoefficient : C ^ 2 = Real.exp (2 * K) := by
    dsimp [C]
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  simpa only [hCoefficient] using hq

end RequestProject.YangMills
