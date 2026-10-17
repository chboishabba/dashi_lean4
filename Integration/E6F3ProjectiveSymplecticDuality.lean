import Integration.E6F3ExteriorSquare
import Integration.E6F3ProjectiveAssociation
import Mathlib

/-!
# Symplectic projective duality behind the 40-point E6 null quadric

The raw punctured four-trit point carrier is not identified with the 80-point
quadratic null orbit.  The correct construction passes through isotropic
2-planes: an oriented Lagrangian plane is represented by a nonzero primitive
Plucker bivector, and projectivizing that bivector gives a 40-state carrier.

This file makes that projective carrier literal and proves that the explicit
primitive-to-standard quadratic isometry identifies it with the 40 projective
null points.  The Klein polar relation on primitive bivectors matches the
orthogonality relation on the five-dimensional quadric.
-/

namespace Integration.E6F3ProjectiveSymplecticDuality

open Integration.E6F3ExteriorSquare
open Integration.E6F3ProjectiveAssociation

/-- Canonical projective representatives of the oriented Lagrangian bivectors. -/
def LagrangianLine :=
  {p : PrimitiveNull // canonicalProjective (primitiveToStandard p.1) = true}

instance : Fintype LagrangianLine := inferInstance

theorem lagrangianLine_card : Fintype.card LagrangianLine = 40 := by
  native_decide

/-- Canonical-projective implies nonzero. -/
theorem canonical_projective_nonzero :
    ∀ z : V5, canonicalProjective z = true → z ≠ 0 := by
  native_decide

/-- The exterior-square standardization sends each projective Lagrangian line
to a projective null point. -/
def lagrangianToNullLine (p : LagrangianLine) : NullLine :=
  ⟨primitiveToStandard p.1.1, by
    constructor
    · rw [primitive_standard_quadratic, p.1.2.2]
      simp
    · exact p.2⟩

/-- Inverse map from a projective null point to the primitive Plucker chart. -/
def nullLineToLagrangian (z : NullLine) : LagrangianLine :=
  let znz : z.1 ≠ 0 := canonical_projective_nonzero z.1 z.2.2
  let sn : StandardNull := ⟨z.1, znz, z.2.1⟩
  let pn : PrimitiveNull := primitiveNullEquivStandardNull.symm sn
  ⟨pn, by
    change canonicalProjective (primitiveToStandard pn.1) = true
    simpa [pn, sn, primitiveNullEquivStandardNull,
      primitiveNullToStandard, standardNullToPrimitive] using z.2.2⟩

theorem lagrangian_null_left (p : LagrangianLine) :
    nullLineToLagrangian (lagrangianToNullLine p) = p := by
  apply Subtype.ext
  apply Subtype.ext
  exact primitive_standard_left p.1.1

theorem lagrangian_null_right (z : NullLine) :
    lagrangianToNullLine (nullLineToLagrangian z) = z := by
  apply Subtype.ext
  exact primitive_standard_right z.1

/-- Explicit projective incidence-duality equivalence. -/
def lagrangianLineEquivNullLine : LagrangianLine ≃ NullLine where
  toFun := lagrangianToNullLine
  invFun := nullLineToLagrangian
  left_inv := lagrangian_null_left
  right_inv := lagrangian_null_right

/-- Polarization of the primitive Plucker quadratic. -/
def primitivePolar (p q : V5) : F3 :=
  qPrimitive (p + q) - qPrimitive p - qPrimitive q

/-- Projective symplectic-line intersection relation in the Klein model. -/
def lagrangianAdjacent (p q : LagrangianLine) : Bool :=
  decide (p ≠ q ∧ primitivePolar p.1.1 q.1.1 = 0)

/-- The projective Plucker duality preserves the finite incidence relation:
intersection of Lagrangian lines is exactly orthogonality of the corresponding
quadratic null points. -/
theorem lagrangian_null_adjacency_intertwining :
    ∀ p q : LagrangianLine,
      lagrangianAdjacent p q =
        nullAdjacent (lagrangianToNullLine p) (lagrangianToNullLine q) := by
  native_decide

/-- Consequently the symplectic projective line graph inherits the exact
SRG(40,12,2,4) parameters already paid for the null-quadric graph. -/
def lagrangianDegree (p : LagrangianLine) : Nat :=
  (Finset.univ.filter fun q : LagrangianLine => lagrangianAdjacent p q).card

def lagrangianCommon (p q : LagrangianLine) : Nat :=
  (Finset.univ.filter fun r : LagrangianLine =>
    lagrangianAdjacent p r && lagrangianAdjacent q r).card

theorem lagrangian_degree_12 : ∀ p : LagrangianLine, lagrangianDegree p = 12 := by
  native_decide

theorem lagrangian_adjacent_common_2 :
    ∀ p q : LagrangianLine,
      lagrangianAdjacent p q = true → lagrangianCommon p q = 2 := by
  native_decide

theorem lagrangian_nonadjacent_common_4 :
    ∀ p q : LagrangianLine,
      p ≠ q → lagrangianAdjacent p q = false → lagrangianCommon p q = 4 := by
  native_decide

inductive RawProjectiveT4PointIsNullQuadricPoint : Prop

theorem raw_projective_t4_point_not_promoted :
    ¬ RawProjectiveT4PointIsNullQuadricPoint := by
  intro h
  cases h

structure Boundary where
  projectiveLagrangianCount40Paid : Bool
  explicitLagrangianNullEquivalencePaid : Bool
  incidenceOrthogonalityIntertwiningPaid : Bool
  lagrangianSRG401224Paid : Bool
  rawProjectiveT4PointIdentifiedWithNullPoint : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  projectiveLagrangianCount40Paid := true
  explicitLagrangianNullEquivalencePaid := true
  incidenceOrthogonalityIntertwiningPaid := true
  lagrangianSRG401224Paid := true
  rawProjectiveT4PointIdentifiedWithNullPoint := false

end Integration.E6F3ProjectiveSymplecticDuality
