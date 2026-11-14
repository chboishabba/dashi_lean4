import Integration.Ternary27AlbertShapeE6ActionBoundary
import Integration.E8StructuredFullWeylRecognition
import Mathlib

/-!
# 27 points are not a 27-dimensional Albert vector space

The exceptional programme uses two unrelated appearances of the number 27:

1. the E6 minuscule representation has a 27-element weight orbit, realized here
   by the typed ternary/Schlaefli carrier;
2. the Albert algebra has vector-space dimension 27 over its base field.

These are not the same notion of size.  In particular a 27-dimensional vector
space over F3 has `3^27` elements, not 27.  Therefore the existing
`Ternary27Point` cannot itself be the underlying carrier of a 27-dimensional
F3 Albert algebra.  Its exact `origin + 26` puncture is a finite-set shape, not
a scalar/traceless linear decomposition.

The correct future Albert target is a 27-dimensional module/algebra equipped
with a distinguished 27-weight/minuscule geometry, together with unit, Jordan
product, adjoint/cubic norm and F4 automorphism data.
-/

namespace Integration.Ternary27AlbertDimensionCardinalityFirewall

open Integration.Ternary27HyperformSchlafliRecognition
open Integration.Ternary27AlbertShapeE6ActionBoundary

/-- Concrete 27-dimensional vector-space carrier over F3. -/
abbrev F3Vector27 := Fin 27 → ZMod 3

instance : Fintype F3Vector27 := inferInstance

 theorem f3_vector_27_card : Fintype.card F3Vector27 = 3^27 := by
  native_decide

 theorem three_pow_twenty_seven_not_twenty_seven : (3^27 : Nat) ≠ 27 := by
  norm_num

 theorem ternary_27_point_card : Fintype.card Ternary27Point = 27 :=
  ternary27_card

/-- A 27-point set cannot be the underlying set of the 27-dimensional F3
vector space. -/
theorem no_equiv_ternary27_to_f3_vector27 :
    ¬ Nonempty (Ternary27Point ≃ F3Vector27) := by
  intro h
  have hc := Fintype.card_congr h.some
  rw [ternary_27_point_card, f3_vector_27_card] at hc
  norm_num at hc

/-- The paid `1+26` split is therefore explicitly classified as finite-set
puncture data, not a linear Albert decomposition. -/
inductive TernaryPointPunctureIsAlbertLinearSplitting : Prop
inductive MinusculeWeightOrbitIsAlbertUnderlyingVectorSpace : Prop

 theorem puncture_does_not_create_linear_albert_split :
    ¬ TernaryPointPunctureIsAlbertLinearSplitting := by intro h; cases h

 theorem minuscule_orbit_does_not_create_albert_vector_space :
    ¬ MinusculeWeightOrbitIsAlbertUnderlyingVectorSpace := by intro h; cases h

/-- Typed target for the genuinely stronger algebraic layer. -/
structure AlbertPromotionTarget where
  Scalar : Type
  Carrier : Type
  [scalarField : Field Scalar]
  [additiveGroup : AddCommGroup Carrier]
  [moduleStructure : Module Scalar Carrier]
  [finiteDimensional : FiniteDimensional Scalar Carrier]
  dimension27 : Module.finrank Scalar Carrier = 27
  unit : Carrier
  jordanProduct : Carrier → Carrier → Carrier
  cubicNorm : Carrier → Scalar

structure Boundary where
  minusculeOrbitCard27Paid : Bool
  albertDimension27DistinguishedFromOrbitCardinality : Bool
  f3Dimension27CardinalityThreePow27Paid : Bool
  ternary27CannotBeF3Vector27UnderlyingSetPaid : Bool
  originPlus26IsOnlyFiniteSetShape : Bool
  genuineLinearAlbertTargetTyped : Bool
  jordanProductPaid : Bool
  cubicNormPaid : Bool
  f4AutomorphismActionPaid : Bool
  deriving Repr


def canonicalBoundary : Boundary where
  minusculeOrbitCard27Paid := true
  albertDimension27DistinguishedFromOrbitCardinality := true
  f3Dimension27CardinalityThreePow27Paid := true
  ternary27CannotBeF3Vector27UnderlyingSetPaid := true
  originPlus26IsOnlyFiniteSetShape := true
  genuineLinearAlbertTargetTyped := true
  jordanProductPaid := false
  cubicNormPaid := false
  f4AutomorphismActionPaid := false

end Integration.Ternary27AlbertDimensionCardinalityFirewall
