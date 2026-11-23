import Integration.Ternary27HyperformSchlafliRecognition
import Integration.AlbertMinusculeWeightLines
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib

/-!
# Existing typed ternary 27 -> scalar + traceless basis, at the linear level

The repository already owns an explicit `Ternary27Point`.  This file splits it
at the literal origin, proves that the complement has 26 points, and shows that
any 26-dimensional traceless Albert carrier admits a basis indexed by those
26 labels.

This closes the carrier/basis part of the old `27 = 1 + 26` observation.  It
does not assert that this arbitrary basis is preserved by F4, matches the E6
minuscule action, or is compatible with the Jordan product/cubic norm.  Those
are the remaining structural transport obligations.
-/

namespace Integration.TernaryAlbertLinearBasisWeld

open Integration.Ternary27HyperformSchlafliRecognition
open Integration.AlbertScalarTraceless
open Integration.AlbertJordanAutomorphism
open Integration.AlbertMinusculeWeightLines

/-- Literal origin of the existing typed ternary cube. -/
def ternaryOrigin : Ternary27Point := ⟨.zero, .zero, .zero⟩

/-- The actual 26 non-origin ternary labels. -/
def NonOrigin26 := {p : Ternary27Point // p ≠ ternaryOrigin}
instance : Fintype NonOrigin26 := inferInstance

/-- Exact complement count. -/
theorem nonorigin_card_26 : Fintype.card NonOrigin26 = 26 := by
  native_decide

/-- Canonical set-theoretic split of the actual ternary 27 at its origin. -/
noncomputable def originSplit : Ternary27Point ≃ (Unit ⊕ NonOrigin26) where
  toFun p := if h : p = ternaryOrigin then Sum.inl () else Sum.inr ⟨p, h⟩
  invFun s := match s with
    | Sum.inl _ => ternaryOrigin
    | Sum.inr q => q.1
  left_inv p := by
    classical
    by_cases h : p = ternaryOrigin
    · simp [h]
    · simp [h]
  right_inv s := by
    classical
    cases s with
    | inl u => cases u; simp
    | inr q => simp [q.2]

/-- The origin really maps to the scalar-side singleton. -/
theorem originSplit_origin : originSplit ternaryOrigin = Sum.inl () := by
  simp [originSplit]

/-- Noncanonical but exact indexing of the 26 labels. -/
noncomputable def nonOriginIndex : NonOrigin26 ≃ Fin 26 :=
  Fintype.equivFinOfCardEq nonorigin_card_26

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

/-- Any finite 26-dimensional traceless carrier admits a `Fin 26` basis. -/
noncomputable def tracelessBasisOfFinrank26
    (A : AlbertStructure J) [Module.Finite ℝ (Traceless A.traceUnit)]
    (h0 : Module.finrank ℝ (Traceless A.traceUnit) = 26) :
    Basis (Fin 26) ℝ (Traceless A.traceUnit) := by
  let e : Traceless A.traceUnit ≃ₗ[ℝ] (Fin 26 → ℝ) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using h0)
  exact (Pi.basisFun ℝ (Fin 26)).map e.symm

/-- Actual inhabitant of the previously typed ternary `1+26` ->
scalar+traceless-basis interface, given only the linear dimension theorem. -/
noncomputable def linearBasisTransport
    (A : AlbertStructure J) [Module.Finite ℝ (Traceless A.traceUnit)]
    (h0 : Module.finrank ℝ (Traceless A.traceUnit) = 26) :
    TernaryOnePlus26BasisTransport A where
  Ternary27 := Ternary27Point
  NonOrigin26 := NonOrigin26
  origin := ternaryOrigin
  splitCarrier := originSplit
  originMapsToScalar := originSplit_origin
  nonOriginIndex := nonOriginIndex
  tracelessBasis := tracelessBasisOfFinrank26 A h0

inductive LinearBasisWeldCreatesF4Equivariance : Prop
inductive LinearBasisWeldCreatesAlbertMultiplicationCompatibility : Prop

theorem linear_basis_weld_does_not_create_f4_equivariance :
    ¬ LinearBasisWeldCreatesF4Equivariance := by
  intro h; cases h

theorem linear_basis_weld_does_not_create_albert_compatibility :
    ¬ LinearBasisWeldCreatesAlbertMultiplicationCompatibility := by
  intro h; cases h

structure Boundary where
  actualTernaryOriginTyped : Bool
  nonOriginCount26Paid : Bool
  originPlus26SplitPaid : Bool
  fin26TracelessBasisFromDimensionPaid : Bool
  linearTernaryBasisTransportInhabited : Bool
  f4EquivariancePaidHere : Bool
  jordanCubicCompatibilityPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  actualTernaryOriginTyped := true
  nonOriginCount26Paid := true
  originPlus26SplitPaid := true
  fin26TracelessBasisFromDimensionPaid := true
  linearTernaryBasisTransportInhabited := true
  f4EquivariancePaidHere := false
  jordanCubicCompatibilityPaidHere := false

end Integration.TernaryAlbertLinearBasisWeld
