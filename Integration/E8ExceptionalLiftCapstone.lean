import Integration.E6F3GeneratedGroupClosure
import Integration.E8TernaryBranchingActionObstruction
import Integration.E8LiteralMixed27Fibres
import Integration.E8LiteralMixed27Transitivity
import Integration.E8LiteralMixed27Schlafli
import Integration.E8Mixed27TernaryTranslationObstruction
import Integration.E6Minuscule27LiteralRecognition
import Integration.E6Minuscule27SchlafliRecognition
import Integration.E6Minuscule27SameObject
import Mathlib

/-!
# Exceptional-lift capstone: E6/F3 -> literal E8 branching -> mixed 27 geometry

This owner records the strongest currently paid exceptional-geometry spine
without promoting the remaining algebraic recognition seams.

Paid independently in the imported owners:

* the five-dimensional mod-3 E6 action has exact quadratic strata 1/80/90/72;
* its six simple generators close to an exact 51,840-element matrix image;
* the literal E8 root system branches under the selected `E6 x A2` subsystem as
  72 E6 roots, 6 A2 roots, and six E6-stable 27-point mixed fibres;
* all six mixed fibres are transitive under the literal E6 reflection relation;
* each mixed 27-fibre carries the Schlaefli `SRG(27,16,10,8)` relation;
* the three positive fibres are exactly the E6 minuscule `omega5` weight orbit,
  while the three negative fibres are exactly the `omega0` orbit;
* the Schlaefli relation itself is recovered from the invariant E6 minuscule
  weight pairing;
* for the canonical plus fibre, the pre-existing Dynkin-label map is an actual
  carrier equivalence with the omega5 minuscule orbit, preserving the Schlaefli
  relation and intertwining the independent reflection relations;
* the earlier count-matched bare ternary branching fails the same-action test;
* the bare additive `F3^3` translation structure cannot realize the Schlaefli
  relation by any undirected translation-invariant Cayley graph.

Still open:

* an Albert/Jordan algebra realization on this now-recognized E6 minuscule
  carrier, including product/cubic-norm data;
* a full ternary 240-state same-action recognition with the literal E8 roots;
* any claim that carrier cardinalities alone realize F4/E6/E7/E8 structure.
-/

namespace Integration.E8ExceptionalLiftCapstone

open Integration.E6F3GeneratedGroupClosure
open Integration.E8LiteralMixed27Fibres
open Integration.E8LiteralMixed27Transitivity
open Integration.E8LiteralMixed27Schlafli
open Integration.E8Mixed27TernaryTranslationObstruction
open Integration.E6Minuscule27LiteralRecognition
open Integration.E6Minuscule27SchlafliRecognition
open Integration.E6Minuscule27SameObject

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

theorem canonical_mixed_fibre_card_paid : Fintype.card Plus0 = 27 :=
  plus0_card

theorem canonical_mixed_fibre_schlafli_degree_paid :
    ∀ x : Plus0, schlafliDegree x = 16 :=
  plus0_degree_16

theorem canonical_mixed_fibre_minuscule_weight_recognition_paid :
    plus0LabelSet = minusculeOmega5Set :=
  plus0_labels_eq_omega5

theorem canonical_mixed_fibre_minuscule_relation_recognition_paid :
    ∀ x y : Plus0,
      schlafliAdjacent x y =
        minusculeAdjacent (fun z : Plus0 => literalDynkinLabel z.1) x y :=
  plus0_schlafli_iff_minuscule_pairing

/-- Stronger same-object result: the literal fibre and minuscule weight orbit
are concretely equivalent via the pre-existing Dynkin-label map. -/
theorem canonical_mixed_fibre_minuscule_same_object_paid :
    Function.Bijective plus0ToOmega5 :=
  plus0_to_omega5_bijective

theorem bare_ternary_translation_route_blocked :
    ∀ mask : Finset Direction, ¬ SchlafliOriginProfile mask :=
  no_translation_invariant_schlafli

inductive FullTernary240SameActionRecognitionPaid : Prop
inductive Albert27AlgebraRecognitionPaid : Prop

theorem full_ternary_240_same_action_not_manufactured :
    ¬ FullTernary240SameActionRecognitionPaid := by
  intro h
  cases h

theorem albert_27_algebra_not_manufactured :
    ¬ Albert27AlgebraRecognitionPaid := by
  intro h
  cases h

structure Boundary where
  e6FiveDimensionalOrbitPartitionPaid : Bool
  e6GeneratedImageOrder51840Paid : Bool
  e6SectorLiteralActionPaid : Bool
  sixMixed27FibresTyped : Bool
  sixMixed27FibresTransitivePaid : Bool
  schlafli27RelationPaid : Bool
  minuscule27WeightOrbitRecognitionPaid : Bool
  minuscule27RelationRecognitionPaid : Bool
  minuscule27SameObjectRecognitionPaid : Bool
  bareTernaryTranslationSchlafliBlocked : Bool
  countMatchedTernaryBranchingActionObstructionPaid : Bool
  fullTernary240SameActionRecognitionPaid : Bool
  albert27AlgebraRecognitionPaid : Bool
  cardinalityAloneCreatesExceptionalRecognition : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  e6FiveDimensionalOrbitPartitionPaid := true
  e6GeneratedImageOrder51840Paid := true
  e6SectorLiteralActionPaid := true
  sixMixed27FibresTyped := true
  sixMixed27FibresTransitivePaid := true
  schlafli27RelationPaid := true
  minuscule27WeightOrbitRecognitionPaid := true
  minuscule27RelationRecognitionPaid := true
  minuscule27SameObjectRecognitionPaid := true
  bareTernaryTranslationSchlafliBlocked := true
  countMatchedTernaryBranchingActionObstructionPaid := true
  fullTernary240SameActionRecognitionPaid := false
  albert27AlgebraRecognitionPaid := false
  cardinalityAloneCreatesExceptionalRecognition := false

end Integration.E8ExceptionalLiftCapstone
