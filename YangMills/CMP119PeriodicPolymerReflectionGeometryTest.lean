import Mathlib
import YangMills.CMP119PeriodicPolymerReflectionGeometry

namespace RequestProject.YangMills

example
    (n : ℕ) [NeZero n] :
    cmp119PeriodicPolymerPlacement n
      (∅ : CMP119PeriodicLinkPolymer n) = CMP119PolymerPlacement.empty := by
  simp [cmp119PeriodicPolymerPlacement,
    cmp119PeriodicPolymerTouchesPositive,
    cmp119PeriodicPolymerTouchesNegative]

example
    (n : ℕ) [NeZero n]
    (X : CMP119PeriodicLinkPolymer n) :
    cmp119PeriodicPolymerPlacement n X = CMP119PolymerPlacement.crossing ↔
      cmp119PeriodicPolymerTouchesPositive n X ∧
      cmp119PeriodicPolymerTouchesNegative n X :=
  cmp119_periodic_polymer_placement_crossing_iff n X

end RequestProject.YangMills
