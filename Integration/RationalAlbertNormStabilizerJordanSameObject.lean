import Integration.RationalAlbertNormUnitRigidityProof

/-!
# Same-object weld: native norm-unit stabilizer = native Jordan automorphism surface

This owner closes the remaining *structural* unit-stabilizer seam on the literal
rational Albert carrier.  It deliberately does not identify either concrete
symmetry object with an abstract algebraic group named `F4` or `E6`.

On the same carrier and the same forward/backward linear maps:

* every Q-linear bijection preserving the native cubic and distinguished unit
  compiles to a Jordan automorphism via the native norm/unit rigidity theorem;
* every Jordan automorphism already carries the same unit/cubic preservation
  fields and therefore forgets to a norm-unit symmetry.

Thus the concrete action classes coincide extensionally.  The remaining theorem
is the classical characteristic-zero algebraic-group/form classification of
those concrete classes.
-/

namespace Integration.RationalAlbertNormStabilizerJordanSameObject

open Integration.RationalAlbertCubicRigidity
open Integration.RationalAlbertNormUnitRigidityProof

abbrev A27 := Integration.RationalAlbertNative.RationalAlbert

/-- Forget a native Jordan automorphism to the underlying cubic-norm symmetry
fixing the distinguished unit.  No new action is introduced. -/
def normUnitOfJordan (g : RationalJordanAutomorphism) : UnitFixingNormSymmetry where
  toRationalLinearBijection := g.toRationalLinearBijection
  map_unit := g.map_unit
  map_cubic := g.map_cubic

/-- Upgrade a native norm-unit symmetry to a Jordan automorphism on the same
literal carrier using the paid norm/unit rigidity theorem. -/
def jordanOfNormUnit (g : UnitFixingNormSymmetry) : RationalJordanAutomorphism :=
  jordanAutomorphismOfNormUnitSymmetry g

@[simp] theorem jordanOfNormUnit_forward (g : UnitFixingNormSymmetry) :
    (jordanOfNormUnit g).forward = g.forward := rfl

@[simp] theorem jordanOfNormUnit_backward (g : UnitFixingNormSymmetry) :
    (jordanOfNormUnit g).backward = g.backward := rfl

@[simp] theorem normUnitOfJordan_forward (g : RationalJordanAutomorphism) :
    (normUnitOfJordan g).forward = g.forward := rfl

@[simp] theorem normUnitOfJordan_backward (g : RationalJordanAutomorphism) :
    (normUnitOfJordan g).backward = g.backward := rfl

/-- Two-way same-action weld: starting from either structural surface and
crossing to the other does not change the actual action on the Albert carrier.
This is the theorem needed by downstream same-object reasoning; equality of
proof fields is intentionally irrelevant. -/
structure SameActionWeld where
  normToJordan : UnitFixingNormSymmetry → RationalJordanAutomorphism
  jordanToNorm : RationalJordanAutomorphism → UnitFixingNormSymmetry
  normForwardPreserved : ∀ g, (normToJordan g).forward = g.forward
  normBackwardPreserved : ∀ g, (normToJordan g).backward = g.backward
  jordanForwardPreserved : ∀ g, (jordanToNorm g).forward = g.forward
  jordanBackwardPreserved : ∀ g, (jordanToNorm g).backward = g.backward

/-- Canonical same-object/action weld on the literal rational Albert carrier. -/
def canonicalSameActionWeld : SameActionWeld where
  normToJordan := jordanOfNormUnit
  jordanToNorm := normUnitOfJordan
  normForwardPreserved := jordanOfNormUnit_forward
  normBackwardPreserved := jordanOfNormUnit_backward
  jordanForwardPreserved := normUnitOfJordan_forward
  jordanBackwardPreserved := normUnitOfJordan_backward

/-- Predicate-level form of the structural equality on one fixed underlying
linear bijection.  This avoids promoting proof-record equality into a stronger
claim than is needed: membership in either action class compiles to membership
in the other without changing the action. -/
structure NormUnitMembership (g : RationalLinearBijection) : Prop where
  map_unit : g.forward Integration.RationalAlbertNative.RationalAlbert.unit =
    Integration.RationalAlbertNative.RationalAlbert.unit
  map_cubic : ∀ x,
    Integration.RationalAlbertNative.RationalAlbert.cubic (g.forward x) =
      Integration.RationalAlbertNative.RationalAlbert.cubic x

structure JordanMembership (g : RationalLinearBijection) : Prop where
  map_unit : g.forward Integration.RationalAlbertNative.RationalAlbert.unit =
    Integration.RationalAlbertNative.RationalAlbert.unit
  map_cubic : ∀ x,
    Integration.RationalAlbertNative.RationalAlbert.cubic (g.forward x) =
      Integration.RationalAlbertNative.RationalAlbert.cubic x
  map_jordan : ∀ x y,
    g.forward (Integration.RationalAlbertNative.RationalAlbert.jordanProduct x y) =
      Integration.RationalAlbertNative.RationalAlbert.jordanProduct
        (g.forward x) (g.forward y)

/-- On the literal carrier, norm+unit membership implies Jordan membership. -/
theorem normUnitMembership_implies_jordanMembership
    (g : RationalLinearBijection) (h : NormUnitMembership g) : JordanMembership g := by
  let n : UnitFixingNormSymmetry :=
    { toRationalLinearBijection := g
      map_unit := h.map_unit
      map_cubic := h.map_cubic }
  let j := jordanOfNormUnit n
  exact
    { map_unit := h.map_unit
      map_cubic := h.map_cubic
      map_jordan := by
        intro x y
        exact j.map_jordan x y }

/-- Conversely, a native Jordan automorphism membership already includes the
same unit and cubic preservation required by the norm-unit stabilizer surface. -/
theorem jordanMembership_implies_normUnitMembership
    (g : RationalLinearBijection) (h : JordanMembership g) : NormUnitMembership g :=
  ⟨h.map_unit, h.map_cubic⟩

/-- Exact predicate equality of the two concrete action classes on every fixed
underlying rational linear bijection. -/
theorem normUnitMembership_iff_jordanMembership (g : RationalLinearBijection) :
    NormUnitMembership g ↔ JordanMembership g :=
  ⟨normUnitMembership_implies_jordanMembership g,
   jordanMembership_implies_normUnitMembership g⟩

structure Boundary where
  sameLiteralCarrier : Bool
  normUnitToJordanCompilerPaid : Bool
  jordanToNormUnitForgetfulPaid : Bool
  sameActionTwoWayWeldPaid : Bool
  membershipIffPaid : Bool
  abstractF4TypeClassificationPaid : Bool
  abstractE6TypeClassificationPaid : Bool
  sourceClassificationCreatesLocalTheorem : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  sameLiteralCarrier := true
  normUnitToJordanCompilerPaid := true
  jordanToNormUnitForgetfulPaid := true
  sameActionTwoWayWeldPaid := true
  membershipIffPaid := true
  abstractF4TypeClassificationPaid := false
  abstractE6TypeClassificationPaid := false
  sourceClassificationCreatesLocalTheorem := false

end Integration.RationalAlbertNormStabilizerJordanSameObject
