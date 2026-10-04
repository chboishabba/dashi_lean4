import Mathlib
import YangMills.LiteralSU2PositiveHalfBoundaryIndependence
import YangMills.LiteralSU2BoundaryGaugeProjectionSymmetry

/-!
# Reflected noncrossing Wilson half reads only the right positive field

The selected reflection swaps the two positive-interior copies and inverts the
temporal boundary.  The positive Wilson half has already been proved independent
of the boundary and of the opposite positive copy.  Composing those two exact
same-object statements closes the final noncrossing locality seam in finite
pure-Wilson OS2.
-/

namespace RequestProject.YangMills

/-- A canonical identity-valued positive-interior field used only to name the half weight. -/
def su2TrivialPositiveInteriorLinks
    (n : ℕ) [NeZero n] : SU2PositiveInteriorLinks n :=
  fun _ => 1

/-- A canonical identity-valued temporal-boundary field used only to name the half weight. -/
def su2TrivialBoundaryTemporalLinks
    (n : ℕ) [NeZero n] : SU2BoundaryTemporalLinks n :=
  fun _ => 1

/-- The positive noncrossing Wilson weight as a function of one positive-interior field. -/
def su2PositiveInteriorWilsonHalfWeight
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (positive : SU2PositiveInteriorLinks n) : ℝ :=
  su2EvenTimePositiveWilsonHalf n
    (su2AssembleReflectedPair n positive
      (su2TrivialBoundaryTemporalLinks n)
      (su2TrivialPositiveInteriorLinks n)) β

/-- The unreflected positive Wilson half is exactly the left half weight. -/
theorem su2_positive_half_assembled_pair_eq_left_weight
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n) :
    su2EvenTimePositiveWilsonHalf n
        (su2AssembleReflectedPair n left boundary right) β =
      su2PositiveInteriorWilsonHalfWeight n β left := by
  unfold su2PositiveInteriorWilsonHalfWeight
  exact su2_positive_half_assembled_pair_boundary_independent
    n β left boundary (su2TrivialBoundaryTemporalLinks n)
      right (su2TrivialPositiveInteriorLinks n)

/--
The reflected positive Wilson half reads only `right`, independently of the
shared temporal-boundary Haar field and independently of `left`.
-/
theorem su2_reflected_positive_half_assembled_pair_eq_right_weight
    (n : ℕ) [NeZero n]
    (β : ℝ)
    (left right : SU2PositiveInteriorLinks n)
    (boundary : SU2BoundaryTemporalLinks n) :
    su2EvenTimePositiveWilsonHalf n
        (su2EvenTimeReflectLinks
          (su2AssembleReflectedPair n left boundary right)) β =
      su2PositiveInteriorWilsonHalfWeight n β right := by
  rw [su2_reflect_assembled_pair n left right boundary]
  unfold su2PositiveInteriorWilsonHalfWeight
  exact su2_positive_half_assembled_pair_boundary_independent
    n β right (su2BoundaryTemporalInvert boundary)
      (su2TrivialBoundaryTemporalLinks n)
      left (su2TrivialPositiveInteriorLinks n)

end RequestProject.YangMills
