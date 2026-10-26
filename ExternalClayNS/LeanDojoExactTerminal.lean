import LeanDojoForceDecayQuantitative
import LeanDojoMomentumTransport
import LeanDojoDivergenceTransport
import LeanDojoEnergyTransport
import LeanDojoSolutionTransport
import Adapter
import Problems.NavierStokes.Millennium

noncomputable section

open MeasureTheory Set
open ClaySpec NavierStokes NavierStokesOnR3

namespace DASHILiteralClayNS

theorem leanDojoR3Solution_to_comparator
    {ν : ℝ} {u₀ : R3 → R3} {f : R3 → ℝ → R3}
    (hν : 0 < ν)
    (hf : NavierStokes.Comparator.ForceConditionDecay f)
    (hdiv : NavierStokesOnR3.DivergenceFreeInitial u₀)
    (sol : GlobalSmoothSolution
      (NavierStokesOnR3.equations ν hν u₀ hdiv (comparatorForceToLean f)))
    (h7 : NavierStokesOnR3.FiniteEnergy sol.velocity) :
    ∃ v p, NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessRn
      ν u₀ f v p := by
  have hforceSmooth :
      ContDiffOn ℝ ∞ (comparatorForceToLean f) (global_spacetime_domain 3) :=
    comparatorDecayForce_smooth hf
  have hClayEnergy : ClaySpec.BoundedEnergy (leanVelocityToClay sol.velocity) := by
    obtain ⟨E, hE⟩ := leanDojoFiniteEnergy_globalBound sol h7
    refine ⟨E, ?_⟩
    intro t ht
    constructor
    · simpa [leanVelocityToClay, leanVelocityToComparator, leanFieldToComparator]
        using leanDojoFiniteEnergy_memLp_velocity sol h7 t ht
    · simpa [leanVelocityToClay, leanVelocityToComparator, leanFieldToComparator]
        using hE t ht
  have hClay : ClaySpec.ClaySolutionR3 ν u₀
      (leanForceToClay (comparatorForceToLean f))
      (leanVelocityToClay sol.velocity)
      (leanPressureToClay sol.pressure) := by
    refine ⟨
      contDiffOn_leanFieldToComparator sol.velocity_smooth,
      contDiffOn_leanFieldToComparator sol.pressure_smooth,
      leanDojoMomentum_to_clayEquationOne sol hforceSmooth,
      leanDojoIncompressible_to_clay sol,
      ?_, hClayEnergy⟩
    intro x
    exact sol.initial_condition x
  have hc := SemanticGap.claySolutionR3_to_comparator hClay
  refine ⟨leanVelocityToComparator sol.velocity,
    leanPressureToComparator sol.pressure, ?_⟩
  simpa [leanForceToClay, leanVelocityToClay, leanPressureToClay,
    SemanticGap.curryField] using hc

theorem leanDojoPeriodicSolution_to_comparator
    {ν : ℝ} {u₀ : R3 → R3} {f : R3 → ℝ → R3}
    (hν : 0 < ν)
    (hf : NavierStokes.Comparator.ForceConditionPeriodic f)
    (hdiv : NavierStokesOnR3.DivergenceFreeInitial u₀)
    (sol : GlobalSmoothSolution
      (NavierStokesPeriodic.equations ν hν u₀ hdiv (comparatorForceToLean f)))
    (hper : NavierStokesPeriodic.PeriodicSolutionFields
      sol.velocity sol.pressure) :
    ∃ v p, NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic
      ν u₀ f v p := by
  have hforceSmooth :
      ContDiffOn ℝ ∞ (comparatorForceToLean f) (global_spacetime_domain 3) :=
    comparatorForceSmooth_to_leanDojo hf.toForceCondition
  have hClay : ClaySpec.ClaySolutionPeriodic ν u₀
      (leanForceToClay (comparatorForceToLean f))
      (leanVelocityToClay sol.velocity)
      (leanPressureToClay sol.pressure) := by
    refine ⟨
      contDiffOn_leanFieldToComparator sol.velocity_smooth,
      contDiffOn_leanFieldToComparator sol.pressure_smooth,
      leanDojoMomentum_to_clayEquationOne sol hforceSmooth,
      leanDojoIncompressible_to_clay sol,
      ?_, ?_, ?_⟩
    · intro x
      exact sol.initial_condition x
    · intro z hz j
      exact leanDojoPeriodicVelocity_to_comparator sol hper z.2 hz z.1 j
    · intro z hz j
      exact leanDojoPeriodicPressure_to_comparator sol hper z.2 hz z.1 j
  have hc := SemanticGap.claySolutionPeriodic_to_comparator hClay
  refine ⟨leanVelocityToComparator sol.velocity,
    leanPressureToComparator sol.pressure, ?_⟩
  simpa [leanForceToClay, leanVelocityToClay, leanPressureToClay,
    SemanticGap.curryField] using hc

theorem dashiExactFeffermanC : MillenniumNavierStokes.FeffermanC := by
  intro ν hν
  obtain ⟨u₀, f, hu₀, hf, hno⟩ := SemanticGapAdapter.openAIComparatorOptionC ν hν
  refine ⟨u₀, comparatorForceToLean f,
    comparatorInitialDecay_to_leanDojo hu₀,
    comparatorInitialDivergence_to_leanDojo hu₀.toInitialVelocityCondition,
    comparatorForceDecay_to_leanDojo hf, ?_⟩
  intro hdiv
  rintro ⟨sol, _h6, h7⟩
  apply hno
  exact leanDojoR3Solution_to_comparator hν hf hdiv sol h7

theorem dashiExactFeffermanD : MillenniumNavierStokes.FeffermanD := by
  intro ν hν
  obtain ⟨u₀, f, hu₀, hf, hno⟩ := SemanticGapAdapter.openAIComparatorOptionD ν hν
  obtain ⟨huSmooth, huPeriodic, huDiv⟩ := comparatorInitialPeriodic_to_leanDojo hu₀
  refine ⟨u₀, comparatorForceToLean f,
    huSmooth, huPeriodic, huDiv,
    comparatorForcePeriodic_to_leanDojo hf,
    comparatorPeriodicForceDecay_to_leanDojo hf, ?_⟩
  intro hdiv
  rintro ⟨sol, hper, _h11⟩
  apply hno
  exact leanDojoPeriodicSolution_to_comparator hν hf hdiv sol hper

#print axioms leanDojoR3Solution_to_comparator
#print axioms leanDojoPeriodicSolution_to_comparator
#print axioms dashiExactFeffermanC
#print axioms dashiExactFeffermanD

end DASHILiteralClayNS
