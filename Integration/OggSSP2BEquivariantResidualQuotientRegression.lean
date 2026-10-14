import Mathlib.Data.ZMod.Basic
import Integration.OggSSP2BEquivariantResidualQuotient

/-!
# Regression: equivariance descends through the residual quotient

This is the RED-first surface for the post-Brauer norm weld.  The production
owner must show that if a surjective quotient presentation and the original
residual map are equivariant, and the descended map commutes with the quotient
presentation, then the descended map is equivariant automatically.
-/

namespace Integration.OggSSP2BEquivariantResidualQuotientRegression

namespace E := Integration.OggSSP2BEquivariantResidualQuotient

inductive G where
  | one
  | sigma
  deriving DecidableEq

abbrev V := Fin 2 → ZMod 2

private def flip (x : V) : V := fun i => x (1 - i)
private def act : G → V → V
  | .one => id
  | .sigma => flip

private def pi : V → V := id
private def residual : V → V := id
private def descended : V → V := id

private theorem pi_surjective : Function.Surjective pi := Function.surjective_id

private theorem descent : ∀ x, descended (pi x) = residual x := by
  intro x
  rfl

private theorem pi_equivariant : E.Equivariant act act pi := by
  intro g x
  rfl

private theorem residual_equivariant : E.Equivariant act act residual := by
  intro g x
  rfl

example : E.Equivariant act act descended :=
  E.equivariant_of_surjective_descent
    pi residual descended pi_surjective descent pi_equivariant residual_equivariant

end Integration.OggSSP2BEquivariantResidualQuotientRegression
