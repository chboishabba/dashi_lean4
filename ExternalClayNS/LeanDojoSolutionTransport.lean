import LeanDojoCoordinateLinearEquiv
import LeanDojoBoundaryExtension
import LeanDojoSameObject

noncomputable section

open ClaySpec
open NavierStokes
open NavierStokesOnR3

namespace DASHILiteralClayNS

theorem leanDojoVelocitySmooth_to_comparator
    {nse : NavierStokesEquations 3}
    (sol : GlobalSmoothSolution nse) :
    ContDiffOn ℝ ∞
      (Function.uncurry (leanVelocityToComparator sol.velocity))
      ((Set.univ : Set R3) ×ˢ Set.Ici (0 : ℝ)) := by
  have h := contDiffOn_leanFieldToComparator sol.velocity_smooth
  simpa [SemanticGap.nonnegativeTime_eq] using h

theorem leanDojoPressureSmooth_to_comparator
    {nse : NavierStokesEquations 3}
    (sol : GlobalSmoothSolution nse) :
    ContDiffOn ℝ ∞
      (Function.uncurry (leanPressureToComparator sol.pressure))
      ((Set.univ : Set R3) ×ˢ Set.Ici (0 : ℝ)) := by
  have h := contDiffOn_leanFieldToComparator sol.pressure_smooth
  simpa [SemanticGap.nonnegativeTime_eq] using h

theorem leanDojoInitialCondition_to_comparator
    {nse : NavierStokesEquations 3}
    (sol : GlobalSmoothSolution nse) :
    ∀ x : R3,
      leanVelocityToComparator sol.velocity x 0 = nse.initial_velocity x := by
  intro x
  exact sol.initial_condition x

theorem leanDojoPeriodic_to_comparatorOnePeriodic
    {α : Type*} {f : R3 → α}
    (h : NavierStokesPeriodic.IsPeriodic f) :
    NavierStokes.Comparator.IsOnePeriodic f := by
  intro x i
  simpa using h x i (1 : ℤ)

theorem leanDojoPeriodicVelocity_to_comparator
    {nse : NavierStokesEquations 3}
    (sol : GlobalSmoothSolution nse)
    (hper : NavierStokesPeriodic.PeriodicSolutionFields
      sol.velocity sol.pressure) :
    ∀ t : ℝ, 0 ≤ t →
      NavierStokes.Comparator.IsOnePeriodic
        (leanVelocityToComparator sol.velocity · t) := by
  intro t ht
  exact leanDojoPeriodic_to_comparatorOnePeriodic (hper.1 t ht)

theorem leanDojoPeriodicPressure_to_comparator
    {nse : NavierStokesEquations 3}
    (sol : GlobalSmoothSolution nse)
    (hper : NavierStokesPeriodic.PeriodicSolutionFields
      sol.velocity sol.pressure) :
    ∀ t : ℝ, 0 ≤ t →
      NavierStokes.Comparator.IsOnePeriodic
        (leanPressureToComparator sol.pressure · t) := by
  intro t ht x i
  have h := hper.2 (spacetime_point t x) ht i (1 : ℤ)
  change
    sol.pressure
        (spacetime_point t (x + EuclideanSpace.single i 1)) =
      sol.pressure (spacetime_point t x)
  simpa [standard_basis] using h

theorem leanDojoSolution_structuralComparatorFields
    {nse : NavierStokesEquations 3}
    (sol : GlobalSmoothSolution nse) :
    (∀ x : R3,
      leanVelocityToComparator sol.velocity x 0 = nse.initial_velocity x) ∧
    ContDiffOn ℝ ∞
      (Function.uncurry (leanVelocityToComparator sol.velocity))
      ((Set.univ : Set R3) ×ˢ Set.Ici (0 : ℝ)) ∧
    ContDiffOn ℝ ∞
      (Function.uncurry (leanPressureToComparator sol.pressure))
      ((Set.univ : Set R3) ×ˢ Set.Ici (0 : ℝ)) :=
  ⟨leanDojoInitialCondition_to_comparator sol,
    leanDojoVelocitySmooth_to_comparator sol,
    leanDojoPressureSmooth_to_comparator sol⟩

end DASHILiteralClayNS
