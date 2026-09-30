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

end RequestProject.YangMills
