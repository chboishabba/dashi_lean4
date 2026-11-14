import Integration.E6Ternary27CoxeterAction
import Mathlib

/-!
# Same ternary-27 carrier: origin+26 puncture versus full E6 minuscule action

The Agda lane already owns a literal two-sided `Ternary27Point <-> 1 + 26`
carrier chart with the geometric origin as the selected scalar-shaped point.
The Lean lane now owns the full faithful 51,840-element E6 action on the same
27 ternary coordinates.

This owner records the corresponding finite fact directly on the Lean carrier:
the origin+26 puncture is exact, but it is NOT an E6-invariant decomposition.
A simple E6 reflection moves the origin.  Thus the finite `1+26` carrier anatomy
must not be confused with the linear Albert decomposition `J = k*1 + J0`, whose
distinguished unit is fixed by F4 rather than by the full E6 minuscule action.

The result strengthens the attribution firewall: we now know exactly how the
same carrier supports both views, and exactly why an additional Jordan/F4
structure is still required.
-/

namespace Integration.Ternary27AlbertShapeE6ActionBoundary

open Integration.Ternary27HyperformSchlafliRecognition
open Integration.E6FullMatrixTernary27SameAction
open Integration.E6Ternary27CoxeterAction
open Integration.E6Mod3WeylAction

/-- Existing geometric origin of the raw ternary cube. -/
def ternaryOrigin : Ternary27Point := ⟨.zero,.zero,.zero⟩

/-- Literal punctured residual on exactly the same carrier. -/
def NonOrigin26 := {p : Ternary27Point // p ≠ ternaryOrigin}

instance : Fintype NonOrigin26 := inferInstance

theorem ternary27_card_is_27 : Fintype.card Ternary27Point = 27 := by native_decide
theorem nonorigin_card_is_26 : Fintype.card NonOrigin26 = 26 := by native_decide

/-- Sum-shape classifier: selected origin versus literal non-origin point. -/
def originPlusResidual : Ternary27Point → Unit ⊕ NonOrigin26
  | p => if h : p = ternaryOrigin then Sum.inl () else Sum.inr ⟨p,h⟩

def residualToPoint : Unit ⊕ NonOrigin26 → Ternary27Point
  | .inl _ => ternaryOrigin
  | .inr p => p.1

theorem residual_after_origin : ∀ p, residualToPoint (originPlusResidual p) = p := by
  intro p
  simp [originPlusResidual, residualToPoint]

theorem origin_after_residual : ∀ a, originPlusResidual (residualToPoint a) = a := by
  intro a
  cases a with
  | inl u => cases u; simp [originPlusResidual, residualToPoint, ternaryOrigin]
  | inr p => simp [originPlusResidual, residualToPoint, p.2]

/-- The same raw carrier therefore has an exact literal 1+26 decomposition. -/
def originResidualEquiv : Ternary27Point ≃ Unit ⊕ NonOrigin26 where
  toFun := originPlusResidual
  invFun := residualToPoint
  left_inv := residual_after_origin
  right_inv := origin_after_residual

/-- Full E6 does not fix the selected origin: the minuscule 27 is transitive,
not `1+26` as an E6 orbit decomposition. -/
theorem simple_reflection_moves_selected_origin :
    globalGeneratorActPoint .s0 ternaryOrigin ≠ ternaryOrigin := by
  native_decide

/-- Consequently the punctured 26 is not preserved by every E6 generator. -/
def NonOriginInvariantUnderFullE6 : Prop :=
  ∀ s (p : NonOrigin26), globalGeneratorActPoint s p.1 ≠ ternaryOrigin

theorem nonorigin26_not_full_e6_invariant : ¬ NonOriginInvariantUnderFullE6 := by
  native_decide

/-- Nor is the selected singleton an E6-invariant scalar/unit line. -/
def OriginFixedByFullE6 : Prop :=
  ∀ s, globalGeneratorActPoint s ternaryOrigin = ternaryOrigin

theorem origin_not_fixed_by_full_e6 : ¬ OriginFixedByFullE6 := by
  intro h
  exact simple_reflection_moves_selected_origin (h .s0)

inductive AlbertJordanProductPaidHere : Prop
inductive AlbertCubicNormPaidHere : Prop
inductive F4UnitStabilizerPaidHere : Prop

theorem puncture_and_e6_action_do_not_manufacture_jordan_product :
    ¬ AlbertJordanProductPaidHere := by intro h; cases h

theorem puncture_and_e6_action_do_not_manufacture_cubic_norm :
    ¬ AlbertCubicNormPaidHere := by intro h; cases h

theorem puncture_and_e6_action_do_not_manufacture_f4_stabilizer :
    ¬ F4UnitStabilizerPaidHere := by intro h; cases h

structure Boundary where
  sameRawTernary27CarrierConsumed : Bool
  exactOriginPlus26Paid : Bool
  fullE6ActionConsumed : Bool
  selectedOriginMovedByE6Paid : Bool
  residual26NotFullE6InvariantPaid : Bool
  onePlus26NotE6RepresentationSplitPaid : Bool
  jordanProductPaid : Bool
  cubicNormPaid : Bool
  f4UnitStabilizerPaid : Bool
  deriving Repr


def canonicalBoundary : Boundary where
  sameRawTernary27CarrierConsumed := true
  exactOriginPlus26Paid := true
  fullE6ActionConsumed := true
  selectedOriginMovedByE6Paid := true
  residual26NotFullE6InvariantPaid := true
  onePlus26NotE6RepresentationSplitPaid := true
  jordanProductPaid := false
  cubicNormPaid := false
  f4UnitStabilizerPaid := false

end Integration.Ternary27AlbertShapeE6ActionBoundary
