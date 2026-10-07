import Mathlib
import YangMills.Path4GaugeEnergyNativeMarkov

/-!
# Path4 gauge-energy compact containment from the native Gibbs moment

This is the direct measure-theoretic completion of the Agda Path4
Markov/sublevel route.

For an actual probability measure mu and nonnegative integrable energy V:
* a moment bound E[V] <= M gives Markov tail M/R;
* if the sublevel K_R={V<R} is compact in the chosen topology, then
  mu(K_R^c) <= M/R.

Thus no independent tightness theorem is needed once a COMMON/projective
configuration topology and compact Path4 energy sublevels are supplied.

The CMP119 wrapper combines this with the literal dyadic residual weld:
a Wilson moment M yields complete-action compact escape at most
  exp(2^{-depth}) M / R.

This does NOT prove the sublevel is compact for the desired continuum gauge
topology. That is now isolated as the geometric/topological producer D2/D5.
-/

namespace RequestProject.YangMills

theorem probability_energy_compact_containment
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
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
          MeasureTheory.Measure Ω)) ≤ M)
    (hCompact : IsCompact {x | energy x < R}) :
    IsCompact {x | energy x < R} ∧
      (((μ : MeasureTheory.ProbabilityMeasure Ω) :
        MeasureTheory.Measure Ω).real
          ({x | energy x < R}ᶜ)) ≤ M / R := by
  refine ⟨hCompact, ?_⟩
  have hTail := probability_energy_markov_div
    μ energy hNonneg hIntegrable M R hR hMoment
  have hSet :
      {x : Ω | energy x < R}ᶜ =
        {x : Ω | R ≤ energy x} := by
    ext x
    simp [not_lt]
  rw [hSet]
  exact hTail

/--
Native complete-CMP119 compact containment, conditional only on:
1. the source-to-literal dyadic residual weld,
2. the Wilson energy moment,
3. native integrability,
4. compactness of the selected Path4 energy sublevel.

The comparison loss is explicit and scale-sensitive.
-/
theorem cmp119_native_dyadic_energy_compact_containment
    (L : ℕ) [NeZero L]
    [TopologicalSpace (SU2TorusLinks L)]
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
          MeasureTheory.Measure (SU2TorusLinks L)))
    (hCompact : IsCompact {links | energy links < R}) :
    IsCompact {links | energy links < R} ∧
      (((su2NativeFiniteGibbsProbability L haar β
        weld.regular weld.rOperation weld.boundary weld.vacuum
        hIntegrableFull :
        MeasureTheory.ProbabilityMeasure (SU2TorusLinks L)) :
        MeasureTheory.Measure (SU2TorusLinks L)).real
        ({links | energy links < R}ᶜ)) ≤
      (Real.exp ((1 / 2 : ℝ) ^ weld.depth) * M) / R := by
  refine ⟨hCompact, ?_⟩
  have hTail :=
    cmp119_native_dyadic_energy_markov
      L weld anchor haar β M R hR energy hEnergyNonnegative
      hIntegrableFull hIntegrableWilson
      hIntegrableFullEnergy hIntegrableWilsonEnergy
      hZFull hZWilson hWilsonMoment
      hNativeEnergyIntegrable
  have hSet :
      {links : SU2TorusLinks L | energy links < R}ᶜ =
        {links : SU2TorusLinks L | R ≤ energy links} := by
    ext links
    simp [not_lt]
  rw [hSet]
  exact hTail

end RequestProject.YangMills
