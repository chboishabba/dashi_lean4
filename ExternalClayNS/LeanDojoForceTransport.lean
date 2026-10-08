import LeanDojoCoordinateLinearEquiv
import LeanDojoSameObject

noncomputable section

open ClaySpec
open NavierStokes
open NavierStokesOnR3

namespace DASHILiteralClayNS

theorem comparatorForceSmooth_to_leanDojo
    {f : R3 → ℝ → R3}
    (h : NavierStokes.Comparator.ForceCondition f) :
    force_smooth_on_global_spacetime_domain (comparatorForceToLean f) := by
  change ContDiffOn ℝ (⊤ : ℕ∞) (comparatorForceToLean f)
    (global_spacetime_domain 3)
  apply contDiffOn_comparatorFieldToLean
  simpa [SemanticGap.nonnegativeTime_eq] using h.smooth

theorem comparatorForcePeriodic_to_leanDojo
    {f : R3 → ℝ → R3}
    (h : NavierStokes.Comparator.ForceConditionPeriodic f) :
    NavierStokesPeriodic.PeriodicForce (comparatorForceToLean f) := by
  intro z hz i n
  have ht : 0 ≤ time z := by
    simpa [global_spacetime_domain, time] using hz
  have hp : NavierStokesPeriodic.IsPeriodic (fun x : R3 => f x (time z)) :=
    comparatorOnePeriodic_to_leanDojo (h.isOnePeriodic (time z) ht)
  have heq := hp (space z) i n
  change
    f (space (z + n • standard_basis (n := 4) i.succ))
        (time (z + n • standard_basis (n := 4) i.succ)) =
      f (space z) (time z)
  simpa using heq

theorem comparatorPeriodicForce_structure
    {f : R3 → ℝ → R3}
    (h : NavierStokes.Comparator.ForceConditionPeriodic f) :
    force_smooth_on_global_spacetime_domain (comparatorForceToLean f) ∧
      NavierStokesPeriodic.PeriodicForce (comparatorForceToLean f) :=
  ⟨comparatorForceSmooth_to_leanDojo h.toForceCondition,
    comparatorForcePeriodic_to_leanDojo h⟩

theorem comparatorDecayForce_smooth
    {f : R3 → ℝ → R3}
    (h : NavierStokes.Comparator.ForceConditionDecay f) :
    force_smooth_on_global_spacetime_domain (comparatorForceToLean f) :=
  comparatorForceSmooth_to_leanDojo h.toForceCondition

end DASHILiteralClayNS
