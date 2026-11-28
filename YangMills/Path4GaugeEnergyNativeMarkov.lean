import Mathlib
import Mathlib.Probability.Moments.Basic
import YangMills.CMP119NativeDyadicMomentBound

/-!
# Native Markov bridge for the Path4 gauge-energy continuum candidate

The Agda T5 route identifies a concrete Path4 gauge-fixed energy as the
preferred coercive observable.  Its pointwise nonnegativity/coercivity are
already source-written there; what remained explicit was the statement that
the selected expectation is an actual probability integral to which ordinary
Markov/sublevel theory applies.

This Lean file proves exactly that measure-theoretic step on Mathlib's native
finite Gibbs ProbabilityMeasure.

For any nonnegative integrable energy V with E_mu[V] <= M,

  R * mu{V >= R} <= M,

and for R>0,

  mu{V >= R} <= M/R.

Combining this with the existing literal CMP119 dyadic transfer yields the
same tail estimate for the complete five-sector Gibbs law from a Wilson-only
moment bound.  The remaining physical source seams are:
* identify V with the selected Path4 gauge-energy observable on SU2TorusLinks;
* prove the Wilson moment bound uniformly in cutoff;
* prove the relevant Path4 energy sublevels are compact in the chosen
  projective/continuum topology.
-/

namespace RequestProject.YangMills

/-- Probability-integral Markov semantics, independent of any abstract T5 expectation carrier. -/
theorem probability_energy_markov
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.ProbabilityMeasure Ω)
    (energy : Ω → ℝ)
    (hNonneg : ∀ x, 0 ≤ energy x)
    (hIntegrable :
      MeasureTheory.Integrable energy
        ((μ : MeasureTheory.ProbabilityMeasure Ω) :
          MeasureTheory.Measure Ω))
    (M R : ℝ)
    (hMoment :
      (∫ x : Ω, energy x
        ∂((μ : MeasureTheory.ProbabilityMeasure Ω) :
          MeasureTheory.Measure Ω)) ≤ M) :
    R *
      (((μ : MeasureTheory.ProbabilityMeasure Ω) :
        MeasureTheory.Measure Ω).real {x | R ≤ energy x}) ≤ M := by
  exact (MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall hNonneg) hIntegrable R).trans hMoment

theorem probability_energy_markov_div
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.ProbabilityMeasure Ω)
    (energy : Ω → ℝ)
    (hNonneg : ∀ x, 0 ≤ energy x)
    (hIntegrable :
      MeasureTheory.Integrable energy
        ((μ : MeasureTheory.ProbabilityMeasure Ω) :
          MeasureTheory.Measure Ω))
    (M R : ℝ) (hR : 0 < R)
    (hMoment :
      (∫ x : Ω, energy x
        ∂((μ : MeasureTheory.ProbabilityMeasure Ω) :
          MeasureTheory.Measure Ω)) ≤ M) :
    (((μ : MeasureTheory.ProbabilityMeasure Ω) :
        MeasureTheory.Measure Ω).real {x | R ≤ energy x}) ≤ M / R := by
  have h := probability_energy_markov
    μ energy hNonneg hIntegrable M R hMoment
  exact (le_div_iff₀ hR).2 (by simpa [mul_comm] using h)

/--
Native CMP119 Path4-tail producer: an actual Wilson moment bound plus the
literal dyadic residual weld gives an explicit complete-Gibbs escape bound.
-/
theorem cmp119_native_dyadic_energy_markov
    (L : ℕ) [NeZero L]
    (weld : CMP119LiteralDyadicResidualWeld L)
    (anchor : SU2TorusLinks L)
    (haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L))
    (β M R : ℝ) (hR : 0 < R)
    (energy : SU2TorusLinks L → ℝ)
    (hEnergyNonnegative : ∀ links, 0 ≤ energy links)
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
    (hIntegrableFullEnergy :
      MeasureTheory.Integrable
        (fun links =>
          su2FourDimensionalCompleteWeight L links β
            weld.regular weld.rOperation weld.boundary weld.vacuum *
            energy links)
        ((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L)))
    (hIntegrableWilsonEnergy :
      MeasureTheory.Integrable
        (fun links =>
          su2PhysicalWilsonWeight L β links * energy links)
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
          su2PhysicalWilsonWeight L β links * energy links
          ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
            MeasureTheory.Measure (SU2TorusLinks L))) /
        (∫ links : SU2TorusLinks L,
          su2PhysicalWilsonWeight L β links
          ∂((haar : MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
            MeasureTheory.Measure (SU2TorusLinks L)))) ≤ M)
    (hNativeEnergyIntegrable :
      MeasureTheory.Integrable energy
        ((su2NativeFiniteGibbsProbability L haar β
          weld.regular weld.rOperation weld.boundary weld.vacuum
          hIntegrableFull :
          MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
          MeasureTheory.Measure (SU2TorusLinks L))) :
    (((su2NativeFiniteGibbsProbability L haar β
        weld.regular weld.rOperation weld.boundary weld.vacuum
        hIntegrableFull :
        MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
        MeasureTheory.Measure (SU2TorusLinks L)).real
      {links | R ≤ energy links}) ≤
      (Real.exp ((1 / 2 : ℝ) ^ weld.depth) * M) / R := by
  have hMoment :=
    cmp119_native_dyadic_coercive_moment_bound
      L weld anchor haar β M energy hEnergyNonnegative
      (by positivity)
      hIntegrableFull hIntegrableWilson
      hIntegrableFullEnergy hIntegrableWilsonEnergy
      hZFull hZWilson hWilsonMoment
  exact probability_energy_markov_div
    (su2NativeFiniteGibbsProbability L haar β
      weld.regular weld.rOperation weld.boundary weld.vacuum
      hIntegrableFull)
    energy hEnergyNonnegative hNativeEnergyIntegrable
    (Real.exp ((1 / 2 : ℝ) ^ weld.depth) * M)
    R hR hMoment

end RequestProject.YangMills
