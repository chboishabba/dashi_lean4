import Mathlib
import YangMills.CMP119DyadicCoerciveMomentTransfer
import YangMills.LiteralSU2NativeGibbsProbability

/-!
# Native CMP119 dyadic moment bound on the actual finite Gibbs probability

This file removes one more representation seam before H2: the dyadic residual
comparison is transported from a partition-function ratio to the actual Mathlib
ProbabilityMeasure constructed from the complete five-sector SU(2) action.

The remaining Clay-facing estimate is therefore genuinely physical:
prove a cutoff-uniform, scale-sensitive Wilson moment bound and instantiate
the selected CMP119 dyadic weld on the same cutoff trajectory.
-/

namespace RequestProject.YangMills

theorem cmp119_native_dyadic_coercive_moment_bound
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
    (∫ links : SU2TorusLinks L, cost links
      ∂((su2NativeFiniteGibbsProbability L haar β
        weld.regular weld.rOperation weld.boundary weld.vacuum
        hIntegrableFull :
        MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
        MeasureTheory.Measure (SU2TorusLinks L))) ≤
      Real.exp ((1 / 2 : ℝ) ^ weld.depth) * M := by
  rw [su2_native_complete_expectation_is_gibbs_ratio
    L haar β weld.regular weld.rOperation weld.boundary weld.vacuum
    hIntegrableFull cost]
  exact cmp119_literal_dyadic_complete_coercive_moment_bound
    L weld anchor haar β M cost hCost hM
    hIntegrableFull hIntegrableWilson
    hIntegrableFullCost hIntegrableWilsonCost
    hZFull hZWilson hWilsonMoment

end RequestProject.YangMills
