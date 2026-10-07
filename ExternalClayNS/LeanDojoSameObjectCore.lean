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

/-- The canonical DASHI/Clay `(space,time)` point as LeanDojo's time-first
four-coordinate spacetime point. -/
def pairToLeanSpacetime (z : SpaceTime) : Spacetime3 :=
  spacetime_point z.2 z.1

/-- Recover the exact `(space,time)` pair from LeanDojo's spacetime carrier. -/
def leanSpacetimeToPair (z : Spacetime3) : SpaceTime :=
  (space z, time z)

@[simp] theorem pairToLeanSpacetime_time (z : SpaceTime) :
    time (pairToLeanSpacetime z) = z.2 := by
  simp [pairToLeanSpacetime, time, spacetime_point]

@[simp] theorem pairToLeanSpacetime_space (z : SpaceTime) :
    space (pairToLeanSpacetime z) = z.1 := by
  ext i
  simp [pairToLeanSpacetime, space, spacetime_point]

@[simp] theorem leanSpacetimeToPair_leftInverse (z : SpaceTime) :
    leanSpacetimeToPair (pairToLeanSpacetime z) = z := by
  apply Prod.ext
  · exact pairToLeanSpacetime_space z
  · exact pairToLeanSpacetime_time z

@[simp] theorem pairToLeanSpacetime_rightInverse (z : Spacetime3) :
    pairToLeanSpacetime (leanSpacetimeToPair z) = z := by
  ext i
  fin_cases i <;>
    simp [pairToLeanSpacetime, leanSpacetimeToPair, spacetime_point, space, time]

/-- Compatibility aliases used by the terminal regression surface. -/
theorem pairToLeanSpacetime_leftInverse :
    Function.LeftInverse leanSpacetimeToPair pairToLeanSpacetime :=
  leanSpacetimeToPair_leftInverse

theorem pairToLeanSpacetime_rightInverse :
    Function.RightInverse leanSpacetimeToPair pairToLeanSpacetime :=
  pairToLeanSpacetime_rightInverse

/-- Exact point equivalence, not merely equal cardinality. -/
def pairLeanSpacetimeEquiv : SpaceTime ≃ Spacetime3 where
  toFun := pairToLeanSpacetime
  invFun := leanSpacetimeToPair
  left_inv := leanSpacetimeToPair_leftInverse
  right_inv := pairToLeanSpacetime_rightInverse

@[simp] theorem pairToLeanSpacetime_nonnegative_iff (z : SpaceTime) :
    pairToLeanSpacetime z ∈ global_spacetime_domain 3 ↔ z ∈ nonnegativeTime := by
  simp [global_spacetime_domain, nonnegativeTime, pairToLeanSpacetime]

@[simp] theorem leanSpacetimeToPair_nonnegative_iff (z : Spacetime3) :
    leanSpacetimeToPair z ∈ nonnegativeTime ↔ z ∈ global_spacetime_domain 3 := by
  simp [global_spacetime_domain, nonnegativeTime, leanSpacetimeToPair, time]

@[simp] theorem pairToLeanSpacetime_positive_iff (z : SpaceTime) :
    pairToLeanSpacetime z ∈ interior_spacetime_domain 3 ↔ 0 < z.2 := by
  simp [interior_spacetime_domain, pairToLeanSpacetime]

/-! ## Field transport -/

/-- Put a curried comparator field on LeanDojo's exact spacetime carrier. -/
def comparatorFieldToLean {E : Type*} (f : R3 → ℝ → E) : Spacetime3 → E :=
  fun z => f (space z) (time z)

/-- Pull a LeanDojo field back to the exact comparator `(space,time)` reading. -/
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
  simp [leanFieldToComparator, comparatorFieldToLean,
    pairToLeanSpacetime, leanSpacetimeToPair,
    pairToLeanSpacetime_rightInverse]

/-- The actual external force carrier used by the C/D transport. -/
abbrev comparatorForceToLean
    (f : R3 → ℝ → R3) : ForceField 3 :=
  comparatorFieldToLean f

/-- LeanDojo velocity pulled back to the comparator carrier. -/
abbrev leanVelocityToComparator
    (u : VelocityField 3) : R3 → ℝ → R3 :=
  leanFieldToComparator u

/-- LeanDojo pressure pulled back to the comparator carrier. -/
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

/-! ## Initial spatial carrier is already definitionally the same object -/

example : ClaySpec.R3 = NavierStokes.Space3 := rfl

/-- Comparator and LeanDojo use the same literal `EuclideanSpace ℝ (Fin 3)`
for the initial velocity carrier. -/
theorem initialVelocityCarrier_sameObject :
    (ClaySpec.R3 → ClaySpec.R3) =
      (NavierStokes.Space3 → NavierStokes.Space3) := rfl

end DASHILiteralClayNS
