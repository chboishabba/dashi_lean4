import Gap
import Problems.NavierStokes.Millennium

/-!
# Exact carrier identification: frozen Clay/comparator spacetime ↔ LeanDojo spacetime

The frozen independent Clay specification uses `R3 × ℝ` (space,time).
LeanDojo uses `EuclideanCoordinateSpace ℝ 4` with time in coordinate `0` and
space in coordinates `1,2,3`.

This file pays that representation identity explicitly.  No PDE, decay, or
existence statement is assumed here: those are transported only after the
underlying points and fields have been shown to be literally recoverable in
both directions.
-/

noncomputable section

open ClaySpec
open NavierStokes

namespace DASHILiteralClayNS

def pairToLeanSpacetime (z : SpaceTime) : Spacetime3 :=
  spacetime_point z.2 z.1

def leanSpacetimeToPair (z : Spacetime3) : SpaceTime :=
  (space z, time z)

@[simp] theorem pairToLeanSpacetime_time (z : SpaceTime) :
    time (pairToLeanSpacetime z) = z.2 := by
  simp [pairToLeanSpacetime, time, spacetime_point]

@[simp] theorem pairToLeanSpacetime_space (z : SpaceTime) :
    space (pairToLeanSpacetime z) = z.1 := by
  ext i
  simp [pairToLeanSpacetime, space, spacetime_point]

@[simp] theorem leanSpacetimeToPair_leftInverse_apply (z : SpaceTime) :
    leanSpacetimeToPair (pairToLeanSpacetime z) = z := by
  apply Prod.ext
  · exact pairToLeanSpacetime_space z
  · exact pairToLeanSpacetime_time z

@[simp] theorem pairToLeanSpacetime_rightInverse_apply (z : Spacetime3) :
    pairToLeanSpacetime (leanSpacetimeToPair z) = z := by
  ext i
  fin_cases i <;>
    simp [pairToLeanSpacetime, leanSpacetimeToPair, spacetime_point, space, time]

theorem pairToLeanSpacetime_leftInverse :
    Function.LeftInverse leanSpacetimeToPair pairToLeanSpacetime :=
  leanSpacetimeToPair_leftInverse_apply

theorem pairToLeanSpacetime_rightInverse :
    Function.RightInverse leanSpacetimeToPair pairToLeanSpacetime :=
  pairToLeanSpacetime_rightInverse_apply

def pairLeanSpacetimeEquiv : SpaceTime ≃ Spacetime3 where
  toFun := pairToLeanSpacetime
  invFun := leanSpacetimeToPair
  left_inv := leanSpacetimeToPair_leftInverse_apply
  right_inv := pairToLeanSpacetime_rightInverse_apply

@[simp] theorem pairToLeanSpacetime_nonnegative_iff (z : SpaceTime) :
    pairToLeanSpacetime z ∈ global_spacetime_domain 3 ↔ z ∈ nonnegativeTime := by
  simp [global_spacetime_domain, nonnegativeTime, pairToLeanSpacetime]

@[simp] theorem leanSpacetimeToPair_nonnegative_iff (z : Spacetime3) :
    leanSpacetimeToPair z ∈ nonnegativeTime ↔ z ∈ global_spacetime_domain 3 := by
  simp [global_spacetime_domain, nonnegativeTime, leanSpacetimeToPair, time]

@[simp] theorem pairToLeanSpacetime_positive_iff (z : SpaceTime) :
    pairToLeanSpacetime z ∈ interior_spacetime_domain 3 ↔ 0 < z.2 := by
  simp [interior_spacetime_domain, pairToLeanSpacetime]

def comparatorFieldToLean {E : Type*} (f : R3 → ℝ → E) : Spacetime3 → E :=
  fun z => f (space z) (time z)

def leanFieldToComparator {E : Type*} (f : Spacetime3 → E) : R3 → ℝ → E :=
  fun x t => f (spacetime_point t x)

@[simp] theorem leanFieldToComparator_comparatorFieldToLean
    {E : Type*} (f : R3 → ℝ → E) :
    leanFieldToComparator (comparatorFieldToLean f) = f := by
  funext x t
  simp [leanFieldToComparator, comparatorFieldToLean, space, time, spacetime_point]

@[simp] theorem comparatorFieldToLean_leanFieldToComparator
    {E : Type*} (f : Spacetime3 → E) :
    comparatorFieldToLean (leanFieldToComparator f) = f := by
  funext z
  change f (pairToLeanSpacetime (leanSpacetimeToPair z)) = f z
  rw [pairToLeanSpacetime_rightInverse_apply]

abbrev comparatorForceToLean
    (f : R3 → ℝ → R3) : ForceField 3 :=
  comparatorFieldToLean f

abbrev leanVelocityToComparator
    (u : VelocityField 3) : R3 → ℝ → R3 :=
  leanFieldToComparator u

abbrev leanPressureToComparator
    (p : PressureField 3) : R3 → ℝ → ℝ :=
  leanFieldToComparator p

@[simp] theorem comparatorForce_roundtrip (f : R3 → ℝ → R3) :
    leanFieldToComparator (comparatorForceToLean f) = f :=
  leanFieldToComparator_comparatorFieldToLean f

@[simp] theorem leanVelocity_roundtrip (u : VelocityField 3) :
    comparatorFieldToLean (leanVelocityToComparator u) = u :=
  comparatorFieldToLean_leanFieldToComparator u

@[simp] theorem leanPressure_roundtrip (p : PressureField 3) :
    comparatorFieldToLean (leanPressureToComparator p) = p :=
  comparatorFieldToLean_leanFieldToComparator p

example : ClaySpec.R3 = NavierStokes.Space3 := rfl

theorem initialVelocityCarrier_sameObject :
    (ClaySpec.R3 → ClaySpec.R3) =
      (NavierStokes.Space3 → NavierStokes.Space3) := rfl

end DASHILiteralClayNS
