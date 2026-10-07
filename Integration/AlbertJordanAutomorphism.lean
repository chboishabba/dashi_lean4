import Integration.AlbertScalarTraceless
import Mathlib

/-!
# Albert structure and the structural F4 target

This file defines the *kind* of object that may legitimately be called the
Albert algebra in the DASHI exceptional lane.  It deliberately does not define
`F4` by dimension 52.  The target is a product/unit/trace/cubic-preserving
linear automorphism object, followed by an explicit recognition with an E6 unit
stabilizer.
-/

namespace Integration.AlbertJordanAutomorphism

open Integration.AlbertScalarTraceless

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

/-- A theorem-facing Albert algebra surface.  `jordanMul` is bilinear by type;
Jordan commutativity, identity, and unit are explicit.  The cubic form is kept
separate from the product and must be homogeneous of degree three. -/
structure AlbertStructure (J : Type*) [AddCommGroup J] [Module ℝ J] where
  traceUnit : TraceUnitData J
  jordanMul : J →ₗ[ℝ] J →ₗ[ℝ] J
  jordan_comm : ∀ x y, jordanMul x y = jordanMul y x
  jordan_identity : ∀ x y,
    jordanMul (jordanMul x x) (jordanMul x y) =
      jordanMul x (jordanMul (jordanMul x x) y)
  unit_left : ∀ x, jordanMul traceUnit.unit x = x
  cubic : J → ℝ
  cubic_unit : cubic traceUnit.unit = 1
  cubic_smul : ∀ r x, cubic (r • x) = r ^ 3 * cubic x

/-- Structural Jordan automorphism candidate.  Trace and cubic preservation are
spelled out because those are the exact data needed by the scalar/traceless and
E6/F4 welding programme. -/
structure JordanAutomorphism (A : AlbertStructure J) where
  toLinearEquiv : J ≃ₗ[ℝ] J
  map_unit : toLinearEquiv A.traceUnit.unit = A.traceUnit.unit
  map_jordan : ∀ x y,
    toLinearEquiv (A.jordanMul x y) =
      A.jordanMul (toLinearEquiv x) (toLinearEquiv y)
  map_trace : ∀ x, A.traceUnit.trace (toLinearEquiv x) = A.traceUnit.trace x
  map_cubic : ∀ x, A.cubic (toLinearEquiv x) = A.cubic x

/-- Any trace-preserving Albert automorphism preserves the traceless subspace. -/
theorem JordanAutomorphism.maps_traceless
    (A : AlbertStructure J) (g : JordanAutomorphism A)
    (x : Traceless A.traceUnit) :
    A.traceUnit.trace (g.toLinearEquiv x.1) = 0 := by
  rw [g.map_trace]
  exact x.property

/-- The inverse ambient equivalence also preserves the traceless subspace; this
is derived from the forward trace-preservation law rather than postulated. -/
theorem JordanAutomorphism.symm_maps_traceless
    (A : AlbertStructure J) (g : JordanAutomorphism A)
    (x : Traceless A.traceUnit) :
    A.traceUnit.trace (g.toLinearEquiv.symm x.1) = 0 := by
  have h := g.map_trace (g.toLinearEquiv.symm x.1)
  have h' :
      A.traceUnit.trace (g.toLinearEquiv.symm x.1) =
        A.traceUnit.trace x.1 := by
    simpa using h.symm
  exact h'.trans x.property

/-- Restrict an Albert automorphism to an actual linear equivalence of the
traceless carrier.  This is the theorem-level reason an eventual F4
identification acts on the 26-dimensional `J₀`. -/
noncomputable def JordanAutomorphism.tracelessLinearEquiv
    (A : AlbertStructure J) (g : JordanAutomorphism A) :
    Traceless A.traceUnit ≃ₗ[ℝ] Traceless A.traceUnit where
  toFun x := ⟨g.toLinearEquiv x.1, g.maps_traceless A x⟩
  invFun x := ⟨g.toLinearEquiv.symm x.1, g.symm_maps_traceless A x⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp
  map_smul' r x := by
    apply Subtype.ext
    simp

/-- Carrier-level recognition target for the statement

  Aut_Jordan(J) ≅ F4 ≅ Stab_E6(1).

No group is manufactured here.  A future producer must supply both explicit
bijections and the action compatibility data. -/
structure E6F4StabilizerRecognition (A : AlbertStructure J) : Type 1 where
  E6Actor : Type
  F4Actor : Type
  e6Action : E6Actor → J ≃ₗ[ℝ] J
  e6PreservesCubic : ∀ g x, A.cubic (e6Action g x) = A.cubic x

  F4ToJordanAut : F4Actor → JordanAutomorphism A
  JordanAutToF4 : JordanAutomorphism A → F4Actor
  f4_left_inverse : ∀ g, JordanAutToF4 (F4ToJordanAut g) = g
  f4_right_inverse : ∀ g, F4ToJordanAut (JordanAutToF4 g) = g

  F4ToUnitStabilizer : F4Actor → {g : E6Actor // e6Action g A.traceUnit.unit = A.traceUnit.unit}
  UnitStabilizerToF4 : {g : E6Actor // e6Action g A.traceUnit.unit = A.traceUnit.unit} → F4Actor
  stabilizer_left_inverse : ∀ g, UnitStabilizerToF4 (F4ToUnitStabilizer g) = g
  stabilizer_right_inverse : ∀ g, F4ToUnitStabilizer (UnitStabilizerToF4 g) = g

inductive Dimension52CreatesF4 : Prop
inductive Minuscule27CreatesAlbertAlgebra : Prop

theorem dimension_52_does_not_create_f4 : ¬ Dimension52CreatesF4 := by
  intro h
  cases h

theorem minuscule_27_does_not_create_albert_algebra : ¬ Minuscule27CreatesAlbertAlgebra := by
  intro h
  cases h

structure Boundary where
  jordanProductTyped : Bool
  jordanIdentityRequired : Bool
  distinguishedUnitRequired : Bool
  cubicNormTyped : Bool
  tracePreservingAutomorphismTyped : Bool
  cubicPreservingAutomorphismTyped : Bool
  tracelessActionRestrictionPaid : Bool
  tracelessActionIsLinearEquivalencePaid : Bool
  f4AutomorphismRecognitionPaidHere : Bool
  e6UnitStabilizerRecognitionPaidHere : Bool
  dimension52CreatesF4 : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  jordanProductTyped := true
  jordanIdentityRequired := true
  distinguishedUnitRequired := true
  cubicNormTyped := true
  tracePreservingAutomorphismTyped := true
  cubicPreservingAutomorphismTyped := true
  tracelessActionRestrictionPaid := true
  tracelessActionIsLinearEquivalencePaid := true
  f4AutomorphismRecognitionPaidHere := false
  e6UnitStabilizerRecognitionPaidHere := false
  dimension52CreatesF4 := false

end Integration.AlbertJordanAutomorphism
