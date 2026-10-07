import Integration.AlbertJordanAutomorphism
import Integration.E6Minuscule27SameObject
import Mathlib

/-!
# E6 minuscule weights -> Albert weight lines

The already-paid object `Omega5Weight` is a 27-element finite Weyl orbit.  An
Albert algebra is a 27-dimensional real vector space.  They are not the same
kind of object.  The correct representation-theoretic weld sends each finite
weight to a one-dimensional weight line in the Albert representation.

This file types that recognition obligation and, separately, the later ternary
`1 + 26` basis transport into the scalar/traceless split.
-/

namespace Integration.AlbertMinusculeWeightLines

open Integration.AlbertScalarTraceless
open Integration.AlbertJordanAutomorphism
open Integration.E6LiteralE8Action
open Integration.E6Minuscule27LiteralRecognition
open Integration.E6Minuscule27SchlafliRecognition
open Integration.E6Minuscule27SameObject

variable {J : Type*} [AddCommGroup J] [Module ℝ J]

/-- Recognition of the 27 finite E6 minuscule weights as 27 distinct
one-dimensional lines in an Albert representation. -/
structure MinusculeWeightLineRecognition (A : AlbertStructure J) : Type 1 where
  weightLine : Omega5Weight → Submodule ℝ J
  lineGenerator : Omega5Weight → J
  lineGenerator_ne_zero : ∀ w, lineGenerator w ≠ 0
  weightLine_eq_span : ∀ w,
    weightLine w = Submodule.span ℝ ({lineGenerator w} : Set J)
  distinctWeightLines : Function.Injective weightLine

  reflectWeight : E6SimpleReflection → Omega5Weight → Omega5Weight
  reflectWeight_label : ∀ s w,
    (reflectWeight s w).1 = reflectLabel s w.1
  e6SimpleAction : E6SimpleReflection → J ≃ₗ[ℝ] J
  actionIntertwinesLines : ∀ s w,
    Submodule.map (e6SimpleAction s).toLinearMap (weightLine w) =
      weightLine (reflectWeight s w)

  lineRelated : Submodule ℝ J → Submodule ℝ J → Prop
  relationIntertwines : ∀ x y,
    lineRelated (weightLine x) (weightLine y) ↔
      minusculeAdjacent (fun z : Omega5Weight => z.1) x y = true

/-- Compose the already-paid literal-E8-fibre/minuscule equivalence with any
future weight-line recognition. -/
def literalPlus0WeightLine
    (A : AlbertStructure J) (R : MinusculeWeightLineRecognition A)
    (r : Plus0) : Submodule ℝ J :=
  R.weightLine (plus0EquivOmega5 r)

/-- Correct type for welding the existing ternary `1 + 26` carrier to an actual
Albert scalar/traceless decomposition.  The 26 finite non-origin labels index a
basis of `J₀`; they are not identified with all vectors of `J₀`. -/
structure TernaryOnePlus26BasisTransport (A : AlbertStructure J) : Type 1 where
  Ternary27 : Type
  NonOrigin26 : Type
  origin : Ternary27
  splitCarrier : Ternary27 ≃ (Unit ⊕ NonOrigin26)
  originMapsToScalar : splitCarrier origin = Sum.inl ()

  nonOriginIndex : NonOrigin26 ≃ Fin 26
  tracelessBasis : Basis (Fin 26) ℝ (Traceless A.traceUnit)

/-- An explicit bridge from the finite non-origin label to its actual traceless
basis vector. -/
def TernaryOnePlus26BasisTransport.tracelessVector
    (A : AlbertStructure J) (T : TernaryOnePlus26BasisTransport A)
    (q : T.NonOrigin26) : Traceless A.traceUnit :=
  T.tracelessBasis (T.nonOriginIndex q)

inductive TwentySevenWeightsEqualAlbertVectorSpace : Prop
inductive TernaryTwentySixLabelsEqualAllTracelessVectors : Prop

 theorem finite_weights_not_vector_space : ¬ TwentySevenWeightsEqualAlbertVectorSpace := by
  intro h
  cases h

 theorem basis_labels_not_all_vectors : ¬ TernaryTwentySixLabelsEqualAllTracelessVectors := by
  intro h
  cases h

structure Boundary where
  finiteMinusculeCarrierAlreadyPaid : Bool
  literalMixed27EquivalentToMinusculeAlreadyPaid : Bool
  weightLineRecognitionTyped : Bool
  oneDimensionalLineWitnessRequired : Bool
  e6LineActionIntertwinerRequired : Bool
  schlafliLineRelationRequired : Bool
  ternaryOriginPlus26TargetsScalarPlusBasis : Bool
  actualWeightLineRecognitionPaidHere : Bool
  actualTernaryAlbertBasisTransportPaidHere : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  finiteMinusculeCarrierAlreadyPaid := true
  literalMixed27EquivalentToMinusculeAlreadyPaid := true
  weightLineRecognitionTyped := true
  oneDimensionalLineWitnessRequired := true
  e6LineActionIntertwinerRequired := true
  schlafliLineRelationRequired := true
  ternaryOriginPlus26TargetsScalarPlusBasis := true
  actualWeightLineRecognitionPaidHere := false
  actualTernaryAlbertBasisTransportPaidHere := false

end Integration.AlbertMinusculeWeightLines
