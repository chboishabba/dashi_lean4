import Integration.EisensteinJZeroCMConcreteExact
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Group.Hom.End

/-!
# Eisenstein-order action on the concrete j=0 point group

The preceding owner proves the genuine point-group relation

    Phi^2 + Phi + 1 = 0.

That is exactly the defining quadratic relation of the same
`QuadraticAlgebra Int (-1) (-1)` used by the norm-shell arithmetic.  Mathlib's
`QuadraticAlgebra.lift` therefore gives a literal ring homomorphism from the
Eisenstein integer carrier into additive endomorphisms of the same concrete
j=0 point group.

Important boundary: a ring action on the selected K-rational point group is
not automatically a faithful embedding of the geometric CM order.  The latter
requires a separate injectivity/geometric-endomorphism payment (naturally on a
suitable geometric point or curve-morphism carrier).
-/

namespace Integration.EisensteinCMOrderActionExact

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroCMConcreteExact

noncomputable section

abbrev JZeroPoint := eisensteinJZeroCurve.Point
abbrev JZeroEnd := AddMonoid.End JZeroPoint

private theorem cmPhi_quadratic_end :
    eisensteinCMEndomorphism * eisensteinCMEndomorphism =
      -(1 : JZeroEnd) - eisensteinCMEndomorphism := by
  ext P
  change eisensteinCMEndomorphism (eisensteinCMEndomorphism P) =
    -P - eisensteinCMEndomorphism P
  have h := Integration.jZeroRotationEndomorphism_quadraticRelation
    eisensteinJZeroCurve eisensteinOmega
    rfl rfl rfl rfl
    eisensteinOmega_cube eisensteinOmega_ne_one P
  abel

private def cmOmegaRoot :
    {u : JZeroEnd //
      u * u = (-1 : Int) • (1 : JZeroEnd) + (-1 : Int) • u} :=
  ⟨eisensteinCMEndomorphism, by
    simpa using cmPhi_quadratic_end⟩

/-- The same `ℤ[ω]` ring used by shell arithmetic acts on the j=0 point group. -/
noncomputable def eisensteinOrderAction : EisensteinQA →+* JZeroEnd :=
  (QuadraticAlgebra.lift cmOmegaRoot).toRingHom

/-- The quadratic-algebra generator is sent to the concrete CM rotation. -/
theorem eisensteinOrderAction_omega :
    eisensteinOrderAction (QuadraticAlgebra.omega : EisensteinQA) =
      eisensteinCMEndomorphism := by
  simp [eisensteinOrderAction, cmOmegaRoot]

/-- Coordinate-level form of the action: `a+bω` acts as `a*id + b*Phi`. -/
theorem eisensteinOrderAction_coordinates (a b : Int) :
    eisensteinOrderAction (asQuadraticAlgebra a b) =
      a • (1 : JZeroEnd) + b • eisensteinCMEndomorphism := by
  ext P
  simp [eisensteinOrderAction, cmOmegaRoot, asQuadraticAlgebra,
    QuadraticAlgebra.lift]

/-- Ring multiplication in the shell carrier is composition of its point-group actions. -/
theorem eisensteinOrderAction_mul (z w : EisensteinQA) :
    eisensteinOrderAction (z * w) =
      eisensteinOrderAction z * eisensteinOrderAction w :=
  map_mul eisensteinOrderAction z w

/-- Ring addition in the shell carrier is pointwise addition of endomorphisms. -/
theorem eisensteinOrderAction_add (z w : EisensteinQA) :
    eisensteinOrderAction (z + w) =
      eisensteinOrderAction z + eisensteinOrderAction w :=
  map_add eisensteinOrderAction z w

/-- These are fail-closed status values, not placeholders for inferred theorems. -/
def rationalPointActionFaithfulPaid : Bool := false

def geometricCMEmbeddingPaid : Bool := false

def endomorphismDegreeEqualsEisensteinNormPaid : Bool := false

def heckeCharacterPaid : Bool := false

def localEulerFactorAgreementPaid : Bool := false

def ellipticLSeriesAgreementPaid : Bool := false

structure EisensteinCMOrderActionBoundary : Prop where
  sameIntegralCarrier : True
  definingQuadraticRelationPaid : True
  ringActionPaid : True
  coordinateActionFormulaPaid : True
  rationalPointActionFaithfulnessNotInferred : rationalPointActionFaithfulPaid = false
  geometricCMEmbeddingNotYetPaid : geometricCMEmbeddingPaid = false
  degreeNormIdentificationNotYetPaid : endomorphismDegreeEqualsEisensteinNormPaid = false
  heckeNotYetPaid : heckeCharacterPaid = false
  eulerAgreementNotYetPaid : localEulerFactorAgreementPaid = false
  lSeriesAgreementNotYetPaid : ellipticLSeriesAgreementPaid = false

end

end Integration.EisensteinCMOrderActionExact
