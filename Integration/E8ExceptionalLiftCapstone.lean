import Integration.E6F3GeneratedGroupClosure
import Integration.E8TernaryBranchingActionObstruction
import Integration.E8LiteralMixed27Fibres
import Integration.E8LiteralMixed27Transitivity
import Integration.E8LiteralMixed27Schlafli
import Integration.E8Mixed27TernaryTranslationObstruction
import Mathlib

/-!
# Exceptional-lift capstone: E6/F3 -> literal E8 branching -> mixed 27 geometry

This owner records the strongest currently paid exceptional-geometry spine
without promoting the remaining same-object recognition seams.

Paid independently in the imported owners:

* the five-dimensional mod-3 E6 action has exact quadratic strata 1/80/90/72;
* its six simple generators close to an exact 51,840-element matrix image;
* the literal E8 root system branches under the selected `E6 x A2` subsystem as
  72 E6 roots, 6 A2 roots, and six E6-stable 27-point mixed fibres;
* all six mixed fibres are transitive under the literal E6 reflection relation;
* each mixed 27-fibre carries the Schlaefli `SRG(27,16,10,8)` relation;
* the earlier count-matched bare ternary branching fails the same-action test;
* the bare additive `F3^3` translation structure cannot realize the Schlaefli
  relation by any undirected translation-invariant Cayley graph.

Still open:

* a same-object recognition of an external Albert/minuscule-27 carrier with one
  literal mixed 27-fibre, preserving both action and relation geometry;
* a full ternary 240-state same-action recognition with the literal E8 roots;
* any claim that carrier cardinalities alone realize F4/E6/E7/E8 structure.
-/

namespace Integration.E8ExceptionalLiftCapstone

open Integration.E6F3GeneratedGroupClosure
open Integration.E8LiteralMixed27Fibres
open Integration.E8LiteralMixed27Transitivity
open Integration.E8LiteralMixed27Schlafli
open Integration.E8Mixed27TernaryTranslationObstruction

/-- Exact orbit-size ledger for the literal `E8 -> E6 x A2` root branching. -/
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

/-- The literal branching arithmetic closes exactly. -/
theorem literal_e8_orbit_ledger_closes :
    literalE8OrbitLedger.total =
      literalE8OrbitLedger.e6RootOrbit +
      literalE8OrbitLedger.a2FixedRoots +
      literalE8OrbitLedger.mixedWeightFibres * literalE8OrbitLedger.eachMixedFibre := by
  norm_num [literalE8OrbitLedger]

/-- Cross-check against the exact generated E6 image. -/
theorem e6_generated_image_order_paid : generatedMatrixSet.card = 51840 :=
  generated_matrix_set_card

/-- One canonical literal mixed fibre really has 27 states. -/
theorem canonical_mixed_fibre_card_paid : Fintype.card Plus0 = 27 :=
  plus0_card

/-- The canonical literal mixed fibre has the Schlaefli degree profile. -/
theorem canonical_mixed_fibre_schlafli_degree_paid :
    ∀ x : Plus0, schlafliDegree x = 16 :=
  plus0_degree_16

/-- The bare additive ternary cube cannot supply the literal mixed-27 relation
geometry through a translation-invariant Cayley graph. -/
theorem bare_ternary_translation_route_blocked :
    ∀ mask : Finset Direction, ¬ SchlafliOriginProfile mask :=
  no_translation_invariant_schlafli

inductive FullTernary240SameActionRecognitionPaid : Prop
inductive Albert27SameActionRecognitionPaid : Prop

 theorem full_ternary_240_same_action_not_manufactured :
    ¬ FullTernary240SameActionRecognitionPaid := by
  intro h
  cases h

 theorem albert_27_same_action_not_manufactured :
    ¬ Albert27SameActionRecognitionPaid := by
  intro h
  cases h

structure Boundary where
  e6FiveDimensionalOrbitPartitionPaid : Bool
  e6GeneratedImageOrder51840Paid : Bool
  e6SectorLiteralActionPaid : Bool
  sixMixed27FibresTyped : Bool
  sixMixed27FibresTransitivePaid : Bool
  schlafli27RelationPaid : Bool
  bareTernaryTranslationSchlafliBlocked : Bool
  countMatchedTernaryBranchingActionObstructionPaid : Bool
  fullTernary240SameActionRecognitionPaid : Bool
  albert27SameActionRecognitionPaid : Bool
  cardinalityAloneCreatesExceptionalRecognition : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  e6FiveDimensionalOrbitPartitionPaid := true
  e6GeneratedImageOrder51840Paid := true
  e6SectorLiteralActionPaid := true
  sixMixed27FibresTyped := true
  sixMixed27FibresTransitivePaid := true
  schlafli27RelationPaid := true
  bareTernaryTranslationSchlafliBlocked := true
  countMatchedTernaryBranchingActionObstructionPaid := true
  fullTernary240SameActionRecognitionPaid := false
  albert27SameActionRecognitionPaid := false
  cardinalityAloneCreatesExceptionalRecognition := false

end Integration.E8ExceptionalLiftCapstone
