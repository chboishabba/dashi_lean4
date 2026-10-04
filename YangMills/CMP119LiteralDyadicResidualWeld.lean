import Mathlib
import YangMills.CMP119DyadicResidualOscillation
import YangMills.LiteralSU2FourDimensionalLattice

/-!
# Literal 4D CMP119 dyadic residual weld

The generic dyadic shell arithmetic is useful only if the selected published
CMP119 localized residual is the SAME object as the non-Wilson residual in
the literal four-dimensional Gibbs action.

This file makes that seam one explicit equality on SU2TorusLinks L.

A weld supplies:
* the actual regular/R/boundary/vacuum functions on literal link fields;
* shell contributions on those SAME link fields;
* a selected shell depth and finite retained shell count;
* exact equality between E+R+B+V and the localized shell tail;
* the source shell oscillation bound.

From those data we derive a pairwise oscillation bound and an anchored
interval for the ACTUAL complete-action residual. Therefore the sharp
normalized Gibbs comparison theorem applies with exponent bounded by the
dyadic width 2^{-depth}.

No claim is made here that CMP119 already proves the weld equality.
-/

namespace RequestProject.YangMills

structure CMP119LiteralDyadicResidualWeld
    (L : ℕ) where
  regular rOperation boundary vacuum : SU2TorusLinks L → ℝ
  shellContribution : ℕ → SU2TorusLinks L → ℝ
  depth count : ℕ
  residualIsLocalizedTail :
    ∀ links,
      su2FullResidual regular rOperation boundary vacuum links =
        finiteLocalizedResidualTail shellContribution depth count links
  shellOscillation :
    ∀ shellDepth x y,
      |shellContribution shellDepth x -
        shellContribution shellDepth y| ≤
          cmp119DyadicShell shellDepth

theorem cmp119_literal_residual_pairwise_oscillation
    {L : ℕ}
    (weld : CMP119LiteralDyadicResidualWeld L)
    (x y : SU2TorusLinks L) :
    |su2FullResidual weld.regular weld.rOperation
          weld.boundary weld.vacuum x -
      su2FullResidual weld.regular weld.rOperation
          weld.boundary weld.vacuum y| ≤
      cmp119DyadicTailMajorant weld.depth := by
  rw [weld.residualIsLocalizedTail x,
    weld.residualIsLocalizedTail y]
  exact finite_localized_residual_oscillation_le_majorant
    weld.shellContribution weld.shellOscillation
    weld.depth weld.count x y

theorem cmp119_literal_residual_interval_from_anchor
    {L : ℕ}
    (weld : CMP119LiteralDyadicResidualWeld L)
    (anchor x : SU2TorusLinks L) :
    su2FullResidual weld.regular weld.rOperation
        weld.boundary weld.vacuum anchor -
        cmp119DyadicTailMajorant weld.depth ≤
      su2FullResidual weld.regular weld.rOperation
        weld.boundary weld.vacuum x ∧
    su2FullResidual weld.regular weld.rOperation
        weld.boundary weld.vacuum x ≤
      su2FullResidual weld.regular weld.rOperation
        weld.boundary weld.vacuum anchor +
        cmp119DyadicTailMajorant weld.depth := by
  rw [weld.residualIsLocalizedTail anchor,
    weld.residualIsLocalizedTail x]
  exact finite_localized_residual_interval_from_anchor
    weld.shellContribution weld.shellOscillation
    weld.depth weld.count anchor x

/--
The interval width paid by normalized expectations is exactly 2^{-depth}.
Large constant vacuum shifts alter the interval centre but not this width.
-/
theorem cmp119_literal_dyadic_residual_interval_width
    {L : ℕ}
    (weld : CMP119LiteralDyadicResidualWeld L) :
    let radius := cmp119DyadicTailMajorant weld.depth
    (radius + radius) = (1 / 2 : ℝ) ^ weld.depth := by
  exact cmp119_anchored_interval_oscillation_width weld.depth

/--
Physical consumer theorem: once the source-to-literal weld exists, the
complete four-sector Gibbs expectation of every positive probe is bounded
by exp(2^{-depth}) times the Wilson-only expectation on the SAME finite
link/Haar carrier.

The integrability and positive-partition assumptions are explicit because
they concern the actual finite measure, not dyadic shell arithmetic.
-/
theorem cmp119_literal_dyadic_complete_vs_wilson_expectation
    (L : ℕ) [NeZero L]
    (weld : CMP119LiteralDyadicResidualWeld L)
    (anchor : SU2TorusLinks L)
    (haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L))
    (β : ℝ)
    (probe : SU2TorusLinks L → ℝ)
    (hProbe : ∀ links, 0 ≤ probe links)
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
    (hIntegrableFullProbe :
      MeasureTheory.Integrable
        (fun links =>
          su2FourDimensionalCompleteWeight L links β
            weld.regular weld.rOperation weld.boundary weld.vacuum *
            probe links)
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
          weld.regular weld.rOperation weld.boundary weld.vacuum
        ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L)))
    (hZWilson : 0 <
      ∫ links : SU2TorusLinks L,
        su2PhysicalWilsonWeight L β links
        ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L))) :
    (∫ links : SU2TorusLinks L,
        su2FourDimensionalCompleteWeight L links β
          weld.regular weld.rOperation weld.boundary weld.vacuum *
          probe links
        ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L))) /
      (∫ links : SU2TorusLinks L,
        su2FourDimensionalCompleteWeight L links β
          weld.regular weld.rOperation weld.boundary weld.vacuum
        ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L))) ≤
    Real.exp ((1 / 2 : ℝ) ^ weld.depth) *
      ((∫ links : SU2TorusLinks L,
          su2PhysicalWilsonWeight L β links * probe links
          ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
            MeasureTheory.Measure (SU2TorusLinks L))) /
        (∫ links : SU2TorusLinks L,
          su2PhysicalWilsonWeight L β links
          ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
            MeasureTheory.Measure (SU2TorusLinks L)))) := by
  let center :=
    su2FullResidual weld.regular weld.rOperation
      weld.boundary weld.vacuum anchor
  let radius := cmp119DyadicTailMajorant weld.depth
  have hInterval :
      ∀ links,
        center - radius ≤
          su2FullResidual weld.regular weld.rOperation
            weld.boundary weld.vacuum links ∧
        su2FullResidual weld.regular weld.rOperation
            weld.boundary weld.vacuum links ≤
          center + radius := by
    intro links
    exact cmp119_literal_residual_interval_from_anchor
      weld anchor links
  have h :=
    su2_complete_normalized_vs_wilson_expectation_of_residual_interval
      L haar β
      (center - radius) (center + radius)
      weld.regular weld.rOperation weld.boundary weld.vacuum
      hInterval probe hProbe
      hIntegrableFull hIntegrableWilson
      hIntegrableFullProbe hIntegrableWilsonProbe
      hZFull hZWilson
  have hwidth :
      (center + radius) - (center - radius) =
        (1 / 2 : ℝ) ^ weld.depth := by
    dsimp [radius]
    have hw := cmp119_anchored_interval_oscillation_width weld.depth
    linarith
  simpa [hwidth] using h

end RequestProject.YangMills
