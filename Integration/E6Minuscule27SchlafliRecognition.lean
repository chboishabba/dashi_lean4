import Integration.E6Minuscule27LiteralRecognition
import Integration.E8LiteralMixed27Schlafli
import Mathlib

/-!
# E6 minuscule weight pairing recovers the literal Schlaefli relation

The preceding owner identifies each literal mixed 27-fibre with one of the two
E6 minuscule Weyl weight orbits at the level of Dynkin labels and simple
reflection action.  This file adds the intrinsic relation geometry.

For Dynkin-label vectors `lambda,mu`, the E6 weight inner product is
`lambda^T A^{-1} mu`, where `A` is the E6 Cartan matrix.  Since `det A = 3`, use
the integral scaling `3 A^{-1}`.  On either 27-element minuscule orbit, distinct
pairs have scaled pairings only `1` and `-2`; the pairing-1 relation is exactly
`SRG(27,16,10,8)`.

On the literal E8 mixed fibre, pairing-1 in Dynkin-label coordinates is exactly
the already-paid Schlaefli adjacency defined by scaled E8 root dot product 4.
Thus the relation geometry is recovered from the E6 minuscule weights rather
than transported arbitrarily through a cardinality bijection.
-/

namespace Integration.E6Minuscule27SchlafliRecognition

open Integration.E6Minuscule27LiteralRecognition
open Integration.E8LiteralMixed27Fibres
open Integration.E8LiteralMixed27Schlafli

/-- Integral matrix `3 * A^{-1}` for the repository's E6 Cartan numbering. -/
def threeCartanInverse (i j : Fin 6) : Int :=
  ![![4,3,5,6,4,2],
    ![3,6,6,9,6,3],
    ![5,6,10,12,8,4],
    ![6,9,12,18,12,6],
    ![4,6,8,12,10,5],
    ![2,3,4,6,5,4]] i j

/-- Three times the invariant E6 weight pairing in Dynkin-label coordinates. -/
def scaledWeightInner (lambda mu : DynkinLabel) : Int :=
  ∑ i : Fin 6, ∑ j : Fin 6, lambda i * threeCartanInverse i j * mu j

/-- The integral inverse really inverts the Cartan matrix up to the scale 3. -/
theorem three_cartan_inverse_identity :
    ∀ i j : Fin 6,
      (∑ k : Fin 6, cartanEntry i k * threeCartanInverse k j) =
        if i = j then 3 else 0 := by
  native_decide

/-- Simple reflections preserve the scaled weight pairing. -/
theorem reflection_preserves_scaled_weight_inner :
    ∀ s lambda mu,
      scaledWeightInner (reflectLabel s lambda) (reflectLabel s mu) =
        scaledWeightInner lambda mu := by
  native_decide

/-- Finite carriers for the two paid minuscule weight orbits. -/
def Omega0Weight := {lambda : DynkinLabel // lambda ∈ minusculeOmega0Set}
def Omega5Weight := {lambda : DynkinLabel // lambda ∈ minusculeOmega5Set}

instance : Fintype Omega0Weight := inferInstance
instance : Fintype Omega5Weight := inferInstance

 theorem omega0_weight_card : Fintype.card Omega0Weight = 27 := by
  native_decide

 theorem omega5_weight_card : Fintype.card Omega5Weight = 27 := by
  native_decide

/-- Intrinsic minuscule adjacency from the invariant weight pairing. -/
def minusculeAdjacent {Carrier : Type*} [DecidableEq Carrier]
    (label : Carrier → DynkinLabel) (x y : Carrier) : Bool :=
  decide (x ≠ y ∧ scaledWeightInner (label x) (label y) = 1)

/-- Distinct omega5 weights have exactly the two expected invariant pairings. -/
theorem omega5_distinct_pairing_profile :
    ∀ x y : Omega5Weight, x ≠ y →
      scaledWeightInner x.1 y.1 = 1 ∨ scaledWeightInner x.1 y.1 = -2 := by
  native_decide

/-- The weight-pairing graph on the omega5 orbit has Schlaefli degree 16. -/
def omega5Degree (x : Omega5Weight) : Nat :=
  (Finset.univ.filter fun y : Omega5Weight =>
    minusculeAdjacent (fun z : Omega5Weight => z.1) x y = true).card

 theorem omega5_degree_16 : ∀ x : Omega5Weight, omega5Degree x = 16 := by
  native_decide

/-- Common-neighbour count on the omega5 weight graph. -/
def omega5Common (x y : Omega5Weight) : Nat :=
  (Finset.univ.filter fun z : Omega5Weight =>
    (minusculeAdjacent (fun t : Omega5Weight => t.1) x z &&
     minusculeAdjacent (fun t : Omega5Weight => t.1) y z) = true).card

 theorem omega5_adjacent_common_10 :
    ∀ x y : Omega5Weight,
      minusculeAdjacent (fun z : Omega5Weight => z.1) x y = true →
      omega5Common x y = 10 := by
  native_decide

 theorem omega5_nonadjacent_common_8 :
    ∀ x y : Omega5Weight, x ≠ y →
      minusculeAdjacent (fun z : Omega5Weight => z.1) x y = false →
      omega5Common x y = 8 := by
  native_decide

/-- On the canonical literal mixed fibre, the E6 invariant weight relation is
exactly the independently defined literal-E8 Schlaefli relation. -/
theorem plus0_schlafli_iff_minuscule_pairing :
    ∀ x y : Plus0,
      schlafliAdjacent x y =
        minusculeAdjacent (fun z : Plus0 => literalDynkinLabel z.1) x y := by
  native_decide

/-- The same relation equality holds on all six literal mixed fibres. -/
theorem plus1_schlafli_iff_minuscule_pairing :
    ∀ x y : Plus1,
      schlafliAdjacent x y =
        minusculeAdjacent (fun z : Plus1 => literalDynkinLabel z.1) x y := by
  native_decide

theorem plus2_schlafli_iff_minuscule_pairing :
    ∀ x y : Plus2,
      schlafliAdjacent x y =
        minusculeAdjacent (fun z : Plus2 => literalDynkinLabel z.1) x y := by
  native_decide

theorem minus0_schlafli_iff_minuscule_pairing :
    ∀ x y : Minus0,
      schlafliAdjacent x y =
        minusculeAdjacent (fun z : Minus0 => literalDynkinLabel z.1) x y := by
  native_decide

theorem minus1_schlafli_iff_minuscule_pairing :
    ∀ x y : Minus1,
      schlafliAdjacent x y =
        minusculeAdjacent (fun z : Minus1 => literalDynkinLabel z.1) x y := by
  native_decide

theorem minus2_schlafli_iff_minuscule_pairing :
    ∀ x y : Minus2,
      schlafliAdjacent x y =
        minusculeAdjacent (fun z : Minus2 => literalDynkinLabel z.1) x y := by
  native_decide

inductive WeightRelationRecognitionCreatesAlbertProduct : Prop

theorem weight_relation_recognition_does_not_create_albert_product :
    ¬ WeightRelationRecognitionCreatesAlbertProduct := by
  intro h
  cases h

structure Boundary where
  integralThreeCartanInversePaid : Bool
  invariantWeightPairingPaid : Bool
  omega5PairingProfilePaid : Bool
  omega5SchlafliParametersPaid : Bool
  literalSixFibreRelationEqualityPaid : Bool
  minusculeWeightGeometryRecognized : Bool
  albertJordanProductPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  integralThreeCartanInversePaid := true
  invariantWeightPairingPaid := true
  omega5PairingProfilePaid := true
  omega5SchlafliParametersPaid := true
  literalSixFibreRelationEqualityPaid := true
  minusculeWeightGeometryRecognized := true
  albertJordanProductPaid := false

end Integration.E6Minuscule27SchlafliRecognition
