import Integration.E6F3GeneratedGroupClosure
import Integration.E6RootStabilizerA5SixSet
import Integration.E8TernaryBranchingActionObstruction
import Integration.E8LiteralMixed27Fibres
import Integration.E8LiteralMixed27Transitivity
import Integration.E8LiteralMixed27Schlafli
import Integration.E8Mixed27TernaryTranslationObstruction
import Integration.E6Minuscule27LiteralRecognition
import Integration.E6Minuscule27SchlafliRecognition
import Integration.E6Minuscule27SameObject
import Integration.Ternary27HyperformSchlafliRecognition
import Mathlib

/-!
# Historical exceptional-lift capstone

This file retains the earlier theorem surface for downstream compatibility.
Its old frontier has now been superseded by:

  `Integration.E8StructuredExceptionalLiftFinalMaxCut`

which additionally pays the selected matrix-stabilizer/face-S6 same-object weld,
the full 51,840 matrix/ternary-27 synchronized action, Coxeter coherence, the
gauge-free 72-chart atlas, and the structured 240-state E6 x A2 branching.

Do not use the historical false frontier flags below as the current project
status; they record what this older tranche itself did not manufacture.
-/

namespace Integration.E8ExceptionalLiftCapstone

open Integration.E6F3GeneratedGroupClosure
open Integration.E6RootStabilizerA5SixSet
open Integration.E8LiteralMixed27Fibres
open Integration.E8LiteralMixed27Transitivity
open Integration.E8LiteralMixed27Schlafli
open Integration.E8Mixed27TernaryTranslationObstruction
open Integration.E6Minuscule27LiteralRecognition
open Integration.E6Minuscule27SchlafliRecognition
open Integration.E6Minuscule27SameObject
open Integration.Ternary27HyperformSchlafliRecognition

structure LiteralE8OrbitLedger where
  total : Nat
  e6RootOrbit : Nat
  a2FixedRoots : Nat
  mixedWeightFibres : Nat
  eachMixedFibre : Nat
  deriving Repr

def literalE8OrbitLedger : LiteralE8OrbitLedger where
  total := 240
  e6RootOrbit := 72
  a2FixedRoots := 6
  mixedWeightFibres := 6
  eachMixedFibre := 27

theorem literal_e8_orbit_ledger_closes :
    literalE8OrbitLedger.total =
      literalE8OrbitLedger.e6RootOrbit +
      literalE8OrbitLedger.a2FixedRoots +
      literalE8OrbitLedger.mixedWeightFibres * literalE8OrbitLedger.eachMixedFibre := by
  norm_num [literalE8OrbitLedger]

theorem e6_generated_image_order_paid : generatedMatrixSet.card = 51840 :=
  generated_matrix_set_card

theorem e6_a5_six_object_sym6_action_paid :
    a5GeneratedTables = allSym6Tables :=
  a5_generated_tables_are_exactly_sym6

theorem canonical_mixed_fibre_card_paid : Fintype.card Plus0 = 27 := plus0_card

theorem canonical_mixed_fibre_schlafli_degree_paid :
    ∀ x : Plus0, schlafliDegree x = 16 := plus0_degree_16

theorem canonical_mixed_fibre_minuscule_weight_recognition_paid :
    plus0LabelSet = minusculeOmega5Set := plus0_labels_eq_omega5

theorem canonical_mixed_fibre_minuscule_relation_recognition_paid :
    ∀ x y : Plus0,
      schlafliAdjacent x y =
        minusculeAdjacent (fun z : Plus0 => literalDynkinLabel z.1) x y :=
  plus0_schlafli_iff_minuscule_pairing

theorem canonical_mixed_fibre_minuscule_same_object_paid :
    Function.Bijective plus0ToOmega5 := plus0_to_omega5_bijective

theorem bare_ternary_translation_route_blocked :
    ∀ mask : Finset Direction, ¬ SchlafliOriginProfile mask :=
  no_translation_invariant_schlafli

theorem typed_ternary27_minuscule_relation_same_object_paid :
    Function.Bijective pointToOmega5 := point_to_omega5_bijective

theorem typed_ternary27_schlafli_degree_paid :
    ∀ x : Ternary27Point, pointDegree pointSchlafli x = 16 :=
  typed_hypervoxel_schlafli_degree_16

theorem typed_ternary27_relation_not_translation_invariant_paid :
    ∃ x y t : Ternary27Point,
      pointSchlafli x y ≠ pointSchlafli (pointAdd x t) (pointAdd y t) :=
  typed_schlafli_is_not_translation_invariant

/-- Historical tranche-local boundary only. -/
structure Boundary where
  e6FiveDimensionalOrbitPartitionPaid : Bool
  e6GeneratedImageOrder51840Paid : Bool
  a5SixObjectSym6ActionPaid : Bool
  e6SectorLiteralActionPaid : Bool
  sixMixed27FibresTyped : Bool
  sixMixed27FibresTransitivePaid : Bool
  schlafli27RelationPaid : Bool
  minuscule27WeightOrbitRecognitionPaid : Bool
  minuscule27RelationRecognitionPaid : Bool
  minuscule27SameObjectRecognitionPaid : Bool
  bareTernaryTranslationSchlafliBlocked : Bool
  typedTernary27AbsoluteSchlafliChartPaid : Bool
  typedTernary27MinusculeRelationSameObjectPaid : Bool
  typedTernary27RelationTranslationInvariant : Bool
  countMatchedTernaryBranchingActionObstructionPaid : Bool
  supersededByStructuredFinalMaxCut : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  e6FiveDimensionalOrbitPartitionPaid := true
  e6GeneratedImageOrder51840Paid := true
  a5SixObjectSym6ActionPaid := true
  e6SectorLiteralActionPaid := true
  sixMixed27FibresTyped := true
  sixMixed27FibresTransitivePaid := true
  schlafli27RelationPaid := true
  minuscule27WeightOrbitRecognitionPaid := true
  minuscule27RelationRecognitionPaid := true
  minuscule27SameObjectRecognitionPaid := true
  bareTernaryTranslationSchlafliBlocked := true
  typedTernary27AbsoluteSchlafliChartPaid := true
  typedTernary27MinusculeRelationSameObjectPaid := true
  typedTernary27RelationTranslationInvariant := false
  countMatchedTernaryBranchingActionObstructionPaid := true
  supersededByStructuredFinalMaxCut := true

end Integration.E8ExceptionalLiftCapstone
