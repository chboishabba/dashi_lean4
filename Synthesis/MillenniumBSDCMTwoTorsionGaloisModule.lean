import Synthesis.MillenniumBSDSelmerShaCohomologicalBoundary
import Mathlib.RepresentationTheory.Continuous.TopRep
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-!
# The full rational 2-torsion Galois module for y^2 = x^3 - x

For E : y^2 = x(x-1)(x+1), all three nonzero 2-torsion points

  (0,0), (1,0), (-1,0)

are rational.  Therefore the abstract E[2] Galois module is the constant
`(Z/2Z)^2` module with trivial absolute-Galois action.

This file constructs that actual `TopRep` object.  The remaining arithmetic
same-object theorem is to identify this constant module with the kernel of
multiplication-by-two on the actual elliptic curve over Qbar, and then identify
the corresponding H^1 Kummer classes with the explicit square-class descent.
-/

namespace Synthesis.Millennium.BSD

abbrev CMTwoTorsionCarrier := ZMod 2 × ZMod 2

instance : TopologicalSpace CMTwoTorsionCarrier := ⊥

instance : DiscreteTopology CMTwoTorsionCarrier := ⟨rfl⟩

instance : IsTopologicalAddGroup CMTwoTorsionCarrier := by infer_instance

instance : ContinuousSMul ℤ CMTwoTorsionCarrier := by infer_instance

/-- The trivial absolute-Galois action on the full rational 2-torsion. -/
noncomputable def cmTwoTorsionRepresentation :
    TopRep ℤ RationalAbsoluteGalois :=
  TopRep.of
    (ContRepresentation.trivial
      ℤ RationalAbsoluteGalois CMTwoTorsionCarrier)

@[simp] theorem cmTwoTorsionRepresentation_action
    (g : RationalAbsoluteGalois)
    (x : CMTwoTorsionCarrier) :
    cmTwoTorsionRepresentation.ρ g x = x := by
  rfl

theorem cmTwoTorsion_exponent_two
    (x : CMTwoTorsionCarrier) :
    (2 : ℕ) • x = 0 := by
  rcases x with ⟨a,b⟩
  ext <;> simp

noncomputable abbrev CMTwoTorsionShaOne :=
  rationalTateShafarevichOne cmTwoTorsionRepresentation

noncomputable abbrev CMTwoTorsionShaTwo :=
  rationalTateShafarevichTwoTorsion cmTwoTorsionRepresentation

/--
The expected abstract labels for the four rational 2-torsion points.
-/
def cmTorsionInfinityLabel : CMTwoTorsionCarrier := (0,0)
def cmTorsionZeroLabel : CMTwoTorsionCarrier := (1,0)
def cmTorsionOneLabel : CMTwoTorsionCarrier := (0,1)
def cmTorsionMinusOneLabel : CMTwoTorsionCarrier := (1,1)

theorem cmTorsionLabels_distinct_01 :
    cmTorsionInfinityLabel ≠ cmTorsionZeroLabel := by decide

theorem cmTorsionLabels_distinct_02 :
    cmTorsionInfinityLabel ≠ cmTorsionOneLabel := by decide

theorem cmTorsionLabels_distinct_03 :
    cmTorsionInfinityLabel ≠ cmTorsionMinusOneLabel := by decide

theorem cmTorsionLabels_add_zero_one :
    cmTorsionZeroLabel + cmTorsionOneLabel = cmTorsionMinusOneLabel := by
  decide

theorem cmTorsionLabels_add_zero_minusOne :
    cmTorsionZeroLabel + cmTorsionMinusOneLabel = cmTorsionOneLabel := by
  decide

theorem cmTorsionLabels_add_one_minusOne :
    cmTorsionOneLabel + cmTorsionMinusOneLabel = cmTorsionZeroLabel := by
  decide

/--
Precise remaining same-object bridge to the actual elliptic 2-torsion.
-/
structure CMTwoTorsionEllipticComparison where
  actualEllipticTwoTorsion : Type
  actualEllipticTwoTorsionAddCommGroup : AddCommGroup actualEllipticTwoTorsion
  carrierEquiv : CMTwoTorsionCarrier ≃+ actualEllipticTwoTorsion
  infinity : actualEllipticTwoTorsion
  zeroTorsion : actualEllipticTwoTorsion
  oneTorsion : actualEllipticTwoTorsion
  minusOneTorsion : actualEllipticTwoTorsion
  infinity_eq : carrierEquiv cmTorsionInfinityLabel = infinity
  zero_eq : carrierEquiv cmTorsionZeroLabel = zeroTorsion
  one_eq : carrierEquiv cmTorsionOneLabel = oneTorsion
  minusOne_eq : carrierEquiv cmTorsionMinusOneLabel = minusOneTorsion

attribute [instance] CMTwoTorsionEllipticComparison.actualEllipticTwoTorsionAddCommGroup

/--
Once the actual elliptic E[2] comparison is supplied, the Sha target in the
previous file can use the concrete trivial representation rather than an
abstract placeholder representation.
-/
noncomputable def cmExplicitSelmerCokernelShaBoundary :
    EllipticShaTwoComparisonBoundary → Type :=
  fun _ => ExplicitTwoSelmerCokernel

end Synthesis.Millennium.BSD
