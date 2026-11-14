import Integration.EisensteinJZeroCMConcreteExact

/-!
RED-first concrete same-object regression.

This pins the arithmetic lineage required by the original Eisenstein thread:
the elliptic field is the fraction field of the exact `ℤ[ω]` carrier already
used by the universal norm-shell theorem, not an unrelated complex model.
-/

namespace Integration.EisensteinJZeroCMConcreteRegression

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroCMConcreteExact

example : eisensteinOmega ^ 3 = 1 := eisensteinOmega_cube
example : eisensteinOmega ≠ 1 := eisensteinOmega_ne_one
example : eisensteinJZeroCurve.j = 0 := eisensteinJZeroCurve_j_eq_zero
example : eisensteinJZeroCurve.Point →+ eisensteinJZeroCurve.Point :=
  eisensteinCMEndomorphism
example (P : eisensteinJZeroCurve.Point) :
    eisensteinCMEndomorphism (eisensteinCMEndomorphism (eisensteinCMEndomorphism P)) = P :=
  eisensteinCMEndomorphism_orderThree P

end Integration.EisensteinJZeroCMConcreteRegression
