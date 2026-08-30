import Mathlib
import AgdaMirror.MonsterOntos
import AgdaMirror.GodelLattice
import AgdaMirror.Vec15Descriptive
import AgdaMirror.ArithmeticIntegerEmbedding
import AgdaMirror.TrackedSupport
import AgdaMirror.ActiveWallStructure
import AgdaMirror.MaxPressure

/-!
# Lean mirror of `DASHI/Arithmetic/ActiveWallBounds.agda` (genuine, fully proved)

Active-wall scaling bounds.  Each local delta is bounded by the tracked maximum
and becomes zero when its non-zero indicator is zero, so summing the pointwise
bound yields `totalPressure ≤ Σ_p (1_{δ_p>0} · maxPressure)`.
-/

namespace AgdaMirror.ActiveWallBounds

open AgdaMirror.MonsterOntos
open AgdaMirror.GodelLattice
open AgdaMirror.Vec15Descriptive
open AgdaMirror.ArithmeticIntegerEmbedding
open AgdaMirror.TrackedSupport
open AgdaMirror.ActiveWallStructure
open AgdaMirror.MaxPressure
open SSP

/-- Each local delta is bounded by the tracked maximum. -/
theorem deltaAt_le_maxPressure (p : SSP) (x y : IntCarrier) :
    deltaAt p x y ≤ maxPressure x y := by
  simp only [maxPressure]
  obtain ⟨h2, h3, h5, h7, h11, h13, h17, h19, h23, h29, h31, h41, h47, h59, h71⟩ :=
    le_max15_all (delta15 x y)
  cases p
  · exact h2
  · exact h3
  · exact h5
  · exact h7
  · exact h11
  · exact h13
  · exact h17
  · exact h19
  · exact h23
  · exact h29
  · exact h31
  · exact h41
  · exact h47
  · exact h59
  · exact h71

/-- A non-zero-scaled upper bound: `a ≤ m → a ≤ (1_{a>0})·m`. -/
theorem nonZeroScaleUpper (a m : Nat) (h : a ≤ m) :
    a ≤ countNonZeroNat a * m := by
  cases a with
  | zero => simp [countNonZeroNat]
  | succ n => simpa [countNonZeroNat] using h

/-- Scaled active-wall contribution. -/
def activeWallScaledAt (p : SSP) (x y : IntCarrier) : Nat :=
  activeWallMaskAt p x y * maxPressure x y

/-- 15-lane scaled vector. -/
def activeWallScaled15 (x y : IntCarrier) : Vec15 Nat :=
  mapPrimes15 (fun p => activeWallScaledAt p x y)

/-- Total scaled pressure. -/
def activeWallScaledPressure (x y : IntCarrier) : Nat := sum (activeWallScaled15 x y)

/-- Each delta is bounded by its scaled active-wall contribution. -/
theorem deltaAt_le_activeWallScaledAt (p : SSP) (x y : IntCarrier) :
    deltaAt p x y ≤ activeWallScaledAt p x y := by
  unfold activeWallScaledAt activeWallMaskAt
  exact nonZeroScaleUpper (deltaAt p x y) (maxPressure x y) (deltaAt_le_maxPressure p x y)

/-- The active-wall scaling bound on total pressure. -/
theorem totalPressure_le_activeWallScaledPressure (x y : IntCarrier) :
    totalPressure x y ≤ activeWallScaledPressure x y := by
  unfold totalPressure activeWallScaledPressure activeWallScaled15 delta15 mapPrimes15 sum
  simp only
  have h := fun p => deltaAt_le_activeWallScaledAt p x y
  have := h p2; have := h p3; have := h p5; have := h p7; have := h p11
  have := h p13; have := h p17; have := h p19; have := h p23; have := h p29
  have := h p31; have := h p41; have := h p47; have := h p59; have := h p71
  omega

end AgdaMirror.ActiveWallBounds
