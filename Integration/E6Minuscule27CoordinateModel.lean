import Integration.E6Minuscule27LineAction
import Mathlib

/-!
# Explicit 27-dimensional coordinate model of the minuscule line action

Let `Omega5Weight` be the already-paid 27-element minuscule orbit.  The free
real coordinate module on this finite carrier gives an honest vector space with
one canonical delta vector per weight.  The simple E6 reflections act linearly
by permuting coordinates.

This is a concrete monomial/permutation vector lift of the *Weyl line action*.
It is not yet identified with the Albert algebra, and it does not assert that
the chosen Weyl representatives have the same scalar/sign normalization as an
Albert/E6 representation.
-/

namespace Integration.E6Minuscule27CoordinateModel

open Integration.E6LiteralE8Action
open Integration.E6Minuscule27SchlafliRecognition
open Integration.E6Minuscule27LineAction

abbrev Coordinate27 := Omega5Weight → ℝ

/-- Standard delta vector attached to a minuscule weight. -/
def deltaWeight (w : Omega5Weight) : Coordinate27 :=
  fun u => if u = w then 1 else 0

/-- Delta vectors are nonzero. -/
theorem deltaWeight_ne_zero : ∀ w, deltaWeight w ≠ 0 := by
  intro w h
  have hw := congrFun h w
  simpa [deltaWeight] using hw

/-- A simple reflection acts on coordinate functions by precomposition with
its involutive permutation of the weight carrier. -/
noncomputable def coordinateReflection (s : E6SimpleReflection) :
    Coordinate27 ≃ₗ[ℝ] Coordinate27 where
  toFun f := fun w => f (reflectOmega5 s w)
  invFun f := fun w => f (reflectOmega5 s w)
  left_inv f := by
    funext w
    change f (reflectOmega5 s (reflectOmega5 s w)) = f w
    rw [reflect_omega5_involutive]
  right_inv f := by
    funext w
    change f (reflectOmega5 s (reflectOmega5 s w)) = f w
    rw [reflect_omega5_involutive]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem reflected_eq_iff
    (s : E6SimpleReflection) (u w : Omega5Weight) :
    reflectOmega5 s u = w ↔ u = reflectOmega5 s w := by
  constructor
  · intro h
    calc
      u = reflectOmega5 s (reflectOmega5 s u) := (reflect_omega5_involutive s u).symm
      _ = reflectOmega5 s w := by rw [h]
  · intro h
    calc
      reflectOmega5 s u = reflectOmega5 s (reflectOmega5 s w) := by rw [h]
      _ = w := reflect_omega5_involutive s w

/-- The linear coordinate action permutes the canonical weight vectors exactly. -/
theorem coordinateReflection_delta :
    ∀ s w,
      coordinateReflection s (deltaWeight w) =
        deltaWeight (reflectOmega5 s w) := by
  intro s w
  funext u
  change (if reflectOmega5 s u = w then 1 else 0) =
    (if u = reflectOmega5 s w then 1 else 0)
  rw [reflected_eq_iff]

/-- The coordinate model therefore supplies a scalar-normalized monomial lift
with all action scalars equal to one.  It is a model of the finite Weyl action,
not yet the Albert realization. -/
noncomputable def coordinateMonomialLift : MonomialVectorLift Coordinate27 where
  weightVector := deltaWeight
  weightVector_ne_zero := deltaWeight_ne_zero
  simpleAction := coordinateReflection
  actionScalar := fun _ _ => 1
  actionScalar_ne_zero := by intro; norm_num
  action_on_weight_vector := by
    intro s w
    simpa using coordinateReflection_delta s w

/-- Canonical constant/scalar direction in the permutation coordinate model. -/
def constantVector : Coordinate27 := fun _ => 1

/-- Every simple reflection fixes the constant direction. -/
theorem coordinateReflection_constant :
    ∀ s, coordinateReflection s constantVector = constantVector := by
  intro s
  rfl

/-- Zero-sum/augmentation condition.  This is a canonical 26-dimensional
candidate subspace once finite-dimensional rank arithmetic is supplied, but it
must not be identified with the irreducible F4 traceless representation merely
from its dimension. -/
def coordinateSum : Coordinate27 →ₗ[ℝ] ℝ where
  toFun f := ∑ w, f w
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' r f := by simp [Finset.mul_sum]

def Augmentation26 : Submodule ℝ Coordinate27 := coordinateSum.ker

structure Boundary where
  coordinateVectorModelPaid : Bool
  deltaVectorsPaid : Bool
  linearSimpleReflectionActionPaid : Bool
  deltaPermutationTheoremPaid : Bool
  constantDirectionFixedPaid : Bool
  augmentationCarrierTyped : Bool
  coordinateModelIdentifiedWithAlbert : Bool
  augmentationIdentifiedWithF4Traceless26 : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  coordinateVectorModelPaid := true
  deltaVectorsPaid := true
  linearSimpleReflectionActionPaid := true
  deltaPermutationTheoremPaid := true
  constantDirectionFixedPaid := true
  augmentationCarrierTyped := true
  coordinateModelIdentifiedWithAlbert := false
  augmentationIdentifiedWithF4Traceless26 := false

end Integration.E6Minuscule27CoordinateModel
