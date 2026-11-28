import Mathlib
import YangMills.CMP119LiteralDyadicResidualWeld

/-!
# Literal CMP119 dyadic transfer of coercive moments

The continuum Prokhorov theorem needs a cutoff-uniform coercive moment bound.
The localized-residual lane can only help if it transports such a bound on the
ACTUAL finite link/Haar carrier.

This file proves that reduction: once the selected CMP119 residual is welded
to the literal dyadic tail, every nonnegative coercive probe has complete-action
expectation bounded by exp(2^{-depth}) times its Wilson-only expectation.

It does NOT manufacture the Wilson coercive estimate.  That is now the
irreducible finite-to-continuum producer: prove a scale-sensitive Wilson bound
and a source-native residual weld whose depth is controlled along the cutoff
trajectory.
-/

namespace RequestProject.YangMills

theorem cmp119_literal_dyadic_complete_coercive_moment_bound
    (L : ℕ) [NeZero L]
    (weld : CMP119LiteralDyadicResidualWeld L)
    (anchor : SU2TorusLinks L)
    (haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L))
    (β M : ℝ)
    (cost : SU2TorusLinks L → ℝ)
    (hCost : ∀ links, 0 ≤ cost links)
    (hM : 0 ≤ M)
    (hIntegrableFull :
      MeasureTheory.Integrable
        (su2FourDimensionalCompleteWeight L · β
          weld.regular weld.rOperation weld.boundary weld.vacuum)
        ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L)))
    (hIntegrableWilson :
      MeasureTheory.Integrable
        (su2PhysicalWilsonWeight L β)
        ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L)))
    (hIntegrableFullCost :
      MeasureTheory.Integrable
        (fun links =>
          su2FourDimensionalCompleteWeight L links β
            weld.regular weld.rOperation weld.boundary weld.vacuum *
            cost links)
        ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L)))
    (hIntegrableWilsonCost :
      MeasureTheory.Integrable
        (fun links =>
          su2PhysicalWilsonWeight L β links * cost links)
        ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L)))
    (hZFull : 0 <
      ∫ links : SU2TorusLinks L,
        su2FourDimensionalCompleteWeight L links β
          weld.regular weld.rOperation weld.boundary weld.vacuum
        ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L)))
    (hZWilson : 0 <
      ∫ links : SU2TorusLinks L,
        su2PhysicalWilsonWeight L β links
        ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L)))
    (hWilsonMoment :
      ((∫ links : SU2TorusLinks L,
          su2PhysicalWilsonWeight L β links * cost links
          ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
            MeasureTheory.Measure (SU2TorusLinks L))) /
        (∫ links : SU2TorusLinks L,
          su2PhysicalWilsonWeight L β links
          ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
            MeasureTheory.Measure (SU2TorusLinks L)))) ≤ M) :
    ((∫ links : SU2TorusLinks L,
        su2FourDimensionalCompleteWeight L links β
          weld.regular weld.rOperation weld.boundary weld.vacuum *
          cost links
        ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L))) /
      (∫ links : SU2TorusLinks L,
        su2FourDimensionalCompleteWeight L links β
          weld.regular weld.rOperation weld.boundary weld.vacuum
        ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L))) ≤
      Real.exp ((1 / 2 : ℝ) ^ weld.depth) * M := by
  have hTransfer :=
    cmp119_literal_dyadic_complete_vs_wilson_expectation
      L weld anchor haar β cost hCost
      hIntegrableFull hIntegrableWilson
      hIntegrableFullCost hIntegrableWilsonCost
      hZFull hZWilson
  exact hTransfer.trans
    (mul_le_mul_of_nonneg_left hWilsonMoment (Real.exp_pos _).le)

/--
A cutoff-independent Wilson moment bound is therefore sufficient at any fixed
source depth.  The comparison constant is explicit and tends to one when the
physical localization depth tends to infinity.
-/
theorem cmp119_literal_dyadic_complete_moment_loss_positive
    (depth : ℕ) :
    0 < Real.exp ((1 / 2 : ℝ) ^ depth) := by
  exact Real.exp_pos _

end RequestProject.YangMills
