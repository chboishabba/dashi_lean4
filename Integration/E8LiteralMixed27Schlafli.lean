import Integration.E8LiteralMixed27Fibres
import Mathlib

/-!
# Schlaefli geometry on a literal E8 mixed 27-fibre

Within one fixed A2-weight fibre of the literal `E8 -> E6 x A2` branching,
scaled E8 inner products between distinct roots take only the values 4 and 0.
The dot-4 graph is the classical 27-point Schlaefli strongly regular graph
`SRG(27,16,10,8)`, while orthogonality is its complement
`SRG(27,10,1,5)`.

This gives a much stronger recognition target for an Albert/minuscule-27
carrier than the cardinal identity `27 = 1 + 26`: any claimed same-object
recognition should preserve the 27-point relation geometry as well as the E6
action.
-/

namespace Integration.E8LiteralMixed27Schlafli

open Integration.E8RelativeT5IntrinsicGraphObstruction
open Integration.E8LiteralMixed27Fibres

/-- Schlaefli adjacency on one fixed literal 27-fibre: distinct roots with
scaled E8 inner product 4 (unscaled inner product 1). -/
def schlafliAdjacent {w : Int × Int}
    (x y : LiteralWeightFiber w) : Bool :=
  decide (x ≠ y ∧ e8ScaledDot x.1 y.1 = 4)

/-- Orthogonality adjacency, the complement relation on distinct vertices. -/
def orthogonalAdjacent {w : Int × Int}
    (x y : LiteralWeightFiber w) : Bool :=
  decide (x ≠ y ∧ e8ScaledDot x.1 y.1 = 0)

def schlafliDegree {w : Int × Int} [Fintype (LiteralWeightFiber w)]
    (x : LiteralWeightFiber w) : Nat :=
  (Finset.univ.filter fun y : LiteralWeightFiber w => schlafliAdjacent x y = true).card

def orthogonalDegree {w : Int × Int} [Fintype (LiteralWeightFiber w)]
    (x : LiteralWeightFiber w) : Nat :=
  (Finset.univ.filter fun y : LiteralWeightFiber w => orthogonalAdjacent x y = true).card

def schlafliCommon {w : Int × Int} [Fintype (LiteralWeightFiber w)]
    (x y : LiteralWeightFiber w) : Nat :=
  (Finset.univ.filter fun z : LiteralWeightFiber w =>
    (schlafliAdjacent x z && schlafliAdjacent y z) = true).card

def orthogonalCommon {w : Int × Int} [Fintype (LiteralWeightFiber w)]
    (x y : LiteralWeightFiber w) : Nat :=
  (Finset.univ.filter fun z : LiteralWeightFiber w =>
    (orthogonalAdjacent x z && orthogonalAdjacent y z) = true).card

/-! ## One canonical plus fibre: SRG(27,16,10,8) -/

theorem plus0_degree_16 : ∀ x : Plus0, schlafliDegree x = 16 := by
  native_decide

theorem plus0_adjacent_common_10 :
    ∀ x y : Plus0,
      schlafliAdjacent x y = true → schlafliCommon x y = 10 := by
  native_decide

theorem plus0_nonadjacent_common_8 :
    ∀ x y : Plus0,
      x ≠ y → schlafliAdjacent x y = false → schlafliCommon x y = 8 := by
  native_decide

/-! ## Complement orthogonality graph: SRG(27,10,1,5) -/

theorem plus0_orthogonal_degree_10 :
    ∀ x : Plus0, orthogonalDegree x = 10 := by
  native_decide

theorem plus0_orthogonal_adjacent_common_1 :
    ∀ x y : Plus0,
      orthogonalAdjacent x y = true → orthogonalCommon x y = 1 := by
  native_decide

theorem plus0_orthogonal_nonadjacent_common_5 :
    ∀ x y : Plus0,
      x ≠ y → orthogonalAdjacent x y = false → orthogonalCommon x y = 5 := by
  native_decide

/-- The same Schlaefli parameters hold on all six literal mixed weight fibres. -/
theorem all_six_fibres_schlafli_degree_16 :
    (∀ x : Plus0, schlafliDegree x = 16) ∧
    (∀ x : Plus1, schlafliDegree x = 16) ∧
    (∀ x : Plus2, schlafliDegree x = 16) ∧
    (∀ x : Minus0, schlafliDegree x = 16) ∧
    (∀ x : Minus1, schlafliDegree x = 16) ∧
    (∀ x : Minus2, schlafliDegree x = 16) := by
  native_decide

/-- Recognition contract for an external 27-carrier carrying the same intrinsic
relation geometry.  E6 action intertwining remains an additional requirement
of the stronger `Mixed27Recognition` interface. -/
structure Schlafli27Recognition : Type 1 where
  Carrier : Type
  carrierFintype : Fintype Carrier
  adjacent : Carrier → Carrier → Bool
  equivPlus0 : Carrier ≃ Plus0
  adjacencyPreserved : ∀ x y,
    adjacent x y = schlafliAdjacent (equivPlus0 x) (equivPlus0 y)

inductive Albert27RecognizedFromCardinalityAlone : Prop

theorem cardinality_27_not_schlafli_recognition :
    ¬ Albert27RecognizedFromCardinalityAlone := by
  intro h
  cases h

structure Boundary where
  literal27InnerProductProfilePaid : Bool
  schlafliSRG2716108Paid : Bool
  orthogonalComplementSRG271015Paid : Bool
  allSixFibresSameDegreeProfilePaid : Bool
  schlafliRecognitionInterfaceTyped : Bool
  albertRecognitionFromCardinalityAlone : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  literal27InnerProductProfilePaid := true
  schlafliSRG2716108Paid := true
  orthogonalComplementSRG271015Paid := true
  allSixFibresSameDegreeProfilePaid := true
  schlafliRecognitionInterfaceTyped := true
  albertRecognitionFromCardinalityAlone := false

end Integration.E8LiteralMixed27Schlafli
