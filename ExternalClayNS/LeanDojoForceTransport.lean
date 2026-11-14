import LeanDojoCoordinateLinearEquiv
import LeanDojoSameObject

/-!
# Force-side structural transport to LeanDojo

This file pays the non-quantitative parts of Fefferman conditions (5), (8), and
(9): closed-half-space smoothness and spatial integer periodicity.  The remaining
force obligation is the quantitative mixed-coordinate derivative decay bound.
-/

noncomputable section

open ClaySpec
open NavierStokes
open NavierStokesOnR3

namespace DASHILiteralClayNS

/-- Comparator closed-half-space smoothness transports through the exact
continuous-linear spacetime equivalence. -/
theorem comparatorForceSmooth_to_leanDojo
    {f : R3 → ℝ → R3}
    (h : NavierStokes.Comparator.ForceCondition f) :
    force_smooth_on_global_spacetime_domain (comparatorForceToLean f) := by
  change ContDiffOn ℝ (⊤ : ℕ∞) (comparatorForceToLean f)
    (global_spacetime_domain 3)
  apply contDiffOn_comparatorFieldToLean
  simpa [SemanticGap.nonnegativeTime_eq] using h.smooth

/-- A spatial unit period of a curried comparator force extends to every integer
translate after putting the force on LeanDojo's spacetime carrier. -/
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

/-- The two already-paid structural coordinates of periodic force admissibility. -/
theorem comparatorPeriodicForce_structure
    {f : R3 → ℝ → R3}
    (h : NavierStokes.Comparator.ForceConditionPeriodic f) :
    force_smooth_on_global_spacetime_domain (comparatorForceToLean f) ∧
      NavierStokesPeriodic.PeriodicForce (comparatorForceToLean f) :=
  ⟨comparatorForceSmooth_to_leanDojo h.toForceCondition,
    comparatorForcePeriodic_to_leanDojo h⟩

/-- Whole-space force smoothness is likewise already paid; only the displayed
coordinate-word rapid-decay estimate remains to inhabit `SmoothRapidDecayForce`. -/
theorem comparatorDecayForce_smooth
    {f : R3 → ℝ → R3}
    (h : NavierStokes.Comparator.ForceConditionDecay f) :
    force_smooth_on_global_spacetime_domain (comparatorForceToLean f) :=
  comparatorForceSmooth_to_leanDojo h.toForceCondition

end DASHILiteralClayNS
