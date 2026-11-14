import Mathlib

namespace Synthesis.ClosedDeSitterBounce

/-- Closed-slicing de Sitter scale factor in units H = 1. -/
def scaleFactor (t : ℝ) : ℝ := Real.cosh t

/-- Its proper-time velocity. -/
def scaleVelocity (t : ℝ) : ℝ := Real.sinh t

/-- The scale factor differentiates to the declared velocity. -/
theorem scaleFactor_hasDerivAt (t : ℝ) :
    HasDerivAt scaleFactor (scaleVelocity t) t := by
  simpa [scaleFactor, scaleVelocity] using Real.hasDerivAt_cosh t

/-- The velocity differentiates back to the scale factor, so a'' = a. -/
theorem scaleVelocity_hasDerivAt (t : ℝ) :
    HasDerivAt scaleVelocity (scaleFactor t) t := by
  simpa [scaleFactor, scaleVelocity] using Real.hasDerivAt_sinh t

/-- Exact k=+1 vacuum Friedmann constraint in H=1 units: a_dot^2 + 1 = a^2. -/
theorem closedFriedmann (t : ℝ) :
    scaleVelocity t ^ 2 + 1 = scaleFactor t ^ 2 := by
  simpa [scaleFactor, scaleVelocity] using (Real.cosh_sq t).symm

@[simp] theorem scaleFactor_zero : scaleFactor 0 = 1 := by
  simp [scaleFactor]

@[simp] theorem scaleVelocity_zero : scaleVelocity 0 = 0 := by
  simp [scaleVelocity]

/-- The bounce radius is globally minimal at t=0. -/
theorem one_le_scaleFactor (t : ℝ) : 1 ≤ scaleFactor t := by
  simpa [scaleFactor] using Real.one_le_cosh t

/-- Away from the bounce instant the closed-slicing scale factor is strictly larger. -/
theorem one_lt_scaleFactor {t : ℝ} (ht : t ≠ 0) : 1 < scaleFactor t := by
  simpa [scaleFactor] using (Real.one_lt_cosh.mpr ht)

/-- This closes the real-differential closed-de-Sitter fixture only. -/
def differentiableClosedDeSitterBounceOwned : Bool := true

/-- The birthmark/history programme still has to derive why its source selects this fixture. -/
def historySectorSelectsThisBounceStillRequired : Bool := true

end Synthesis.ClosedDeSitterBounce
