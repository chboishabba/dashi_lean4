import Integration.E6SelectedStabilizerFaceSameObject
import Integration.Ternary27HyperformSchlafliRecognition
import Mathlib

/-!
# Full E6 mod-3 matrix image <-> typed ternary-27 same-action closure

The selected A5/S6 chart stabilizer is already realized directly by absolute
six-face reorganisation.  This owner pays the global finite action weld.

For each of the six E6 simple reflections we record its permutation on the same
27 Schlaefli/minuscule labels already attached to the raw ternary hypervoxel.
Those tables are checked against the independent Dynkin-label reflection law.
We then close MATRIX/PERMUTATION PAIRS synchronously under the same six words.

Exact finite closure gives 51,840 pairs, 51,840 distinct matrix projections and
51,840 distinct 27-permutation projections.  Thus every generated mod-3 matrix
has one and only one generated 27-point action, and conversely.  This is the
global same-action graph; it does not assert an Albert product or a Monster
normalizer realization.
-/

namespace Integration.E6FullMatrixTernary27SameAction

open Integration.E6F3GeneratedGroupClosure
open Integration.E6Mod3WeylAction
open Integration.E6Minuscule27LiteralRecognition
open Integration.Ternary27HyperformSchlafliRecognition
open Integration.Ternary27A5SixFaceReorganisation
open Integration.E6SelectedStabilizerFaceSameObject

abbrev PointIndex := Fin 27
abbrev PointTable := PointIndex → PointIndex

/-- Canonical numbering of the paid 6+15+6 labels. -/
def labelIndex : SchlafliLabel → PointIndex
  | .left f => ⟨(faceIndex f).1, by omega⟩
  | .middle p => ⟨6 + p.1, by omega⟩
  | .right f => ⟨21 + (faceIndex f).1, by omega⟩

/-- Inverse numbering, written literally so the global action remains executable. -/
def indexLabel : PointIndex → SchlafliLabel :=
  ![ .left .xNeg, .left .xPos, .left .yNeg, .left .yPos, .left .zNeg, .left .zPos,
     .middle 0, .middle 1, .middle 2, .middle 3, .middle 4,
     .middle 5, .middle 6, .middle 7, .middle 8, .middle 9,
     .middle 10, .middle 11, .middle 12, .middle 13, .middle 14,
     .right .xNeg, .right .xPos, .right .yNeg, .right .yPos, .right .zNeg, .right .zPos ]

theorem label_index_left : ∀ l, indexLabel (labelIndex l) = l := by native_decide
theorem label_index_right : ∀ i, labelIndex (indexLabel i) = i := by native_decide


def pointIndex (p : Ternary27Point) : PointIndex := labelIndex (pointToLabel p)
def indexPoint (i : PointIndex) : Ternary27Point := labelToPoint (indexLabel i)

theorem point_index_left : ∀ p, indexPoint (pointIndex p) = p := by native_decide
theorem point_index_right : ∀ i, pointIndex (indexPoint i) = i := by native_decide

/-- Exact simple-reflection permutations on the numbered 27-point carrier.
They were generated from the already-paid Dynkin-label reflection law; Lean
checks that provenance below rather than trusting the table. -/
def generatorPointTable : E6SimpleReflection → PointTable
  | .s0 => ![21,22,23,24,25,26,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,0,1,2,3,4,5]
  | .s1 => ![5,1,2,3,4,0,16,7,13,18,20,11,12,8,14,15,6,17,9,19,10,26,22,23,24,25,21]
  | .s2 => ![16,14,2,3,4,6,5,25,8,9,10,11,12,13,1,15,0,24,18,23,20,21,22,19,17,7,26]
  | .s3 => ![2,1,0,3,4,5,11,10,8,9,7,6,12,17,18,15,16,13,14,19,20,23,22,21,24,25,26]
  | .s4 => ![0,1,3,2,4,5,6,7,8,10,9,12,11,13,14,15,16,19,20,17,18,21,22,24,23,25,26]
  | .s5 => ![0,1,2,4,3,5,6,17,20,9,13,11,15,10,14,12,16,7,18,19,8,21,22,23,25,24,26]

/-- Direct raw-point action of the six global E6 generators. -/
def globalGeneratorActPoint (s : E6SimpleReflection) (p : Ternary27Point) : Ternary27Point :=
  indexPoint (generatorPointTable s (pointIndex p))

/-- Independent provenance check: the hard finite tables implement precisely the
existing E6 Dynkin-label reflection, not an arbitrary 27-permutation fit. -/
theorem generator_point_table_intertwines_minuscule_labels :
    ∀ s p,
      labelWeight (pointToLabel (globalGeneratorActPoint s p)) =
        reflectLabel s (labelWeight (pointToLabel p)) := by
  native_decide

/-- Hence every global simple generator preserves the already-paid Schlaefli relation. -/
theorem global_generators_preserve_schlafli :
    ∀ s x y,
      pointSchlafli (globalGeneratorActPoint s x) (globalGeneratorActPoint s y) =
        pointSchlafli x y := by
  native_decide

/-- The direct local A5 action and the global tables agree on all five A5 roots.
This is a local independent check, not the definition of the global action. -/
def a5AsGlobalWordPoint : A5Simple → Ternary27Point → Ternary27Point
  | .a1 => globalGeneratorActPoint .s1
  | .a3 => globalGeneratorActPoint .s3
  | .a4 => globalGeneratorActPoint .s4
  | .a5 => globalGeneratorActPoint .s5
  | .beta => fun p =>
      -- beta is not a simple E6 node; retain the already direct six-face action.
      actPoint .beta p

 theorem four_simple_a5_actions_agree_directly :
    (∀ p, a5AsGlobalWordPoint .a1 p = actPoint .a1 p) ∧
    (∀ p, a5AsGlobalWordPoint .a3 p = actPoint .a3 p) ∧
    (∀ p, a5AsGlobalWordPoint .a4 p = actPoint .a4 p) ∧
    (∀ p, a5AsGlobalWordPoint .a5 p = actPoint .a5 p) := by
  native_decide

/-! ## Full synchronized closure -/

abbrev FullSyncPair := Mat5 × PointTable

def pointTableId : PointTable := fun i => i

def pointTableComp (f g : PointTable) : PointTable := fun i => f (g i)

def fullSyncId : FullSyncPair := (identityMatrix, pointTableId)

def fullSyncLeftMultiply (s : E6SimpleReflection) (x : FullSyncPair) : FullSyncPair :=
  (matrixComp (generatorMatrix s) x.1, pointTableComp (generatorPointTable s) x.2)


def expandFullSync (S : Finset FullSyncPair) : Finset FullSyncPair :=
  S ∪ S.image (fullSyncLeftMultiply .s0) ∪
      S.image (fullSyncLeftMultiply .s1) ∪
      S.image (fullSyncLeftMultiply .s2) ∪
      S.image (fullSyncLeftMultiply .s3) ∪
      S.image (fullSyncLeftMultiply .s4) ∪
      S.image (fullSyncLeftMultiply .s5)


def fullSyncOrbitN : Nat → Finset FullSyncPair
  | 0 => {fullSyncId}
  | n + 1 => expandFullSync (fullSyncOrbitN n)

/-- Same radius as the independently-paid matrix closure. -/
def fullSynchronizedGraph : Finset FullSyncPair := fullSyncOrbitN 36

 theorem full_synchronized_graph_card : fullSynchronizedGraph.card = 51840 := by
  native_decide

 theorem full_synchronized_graph_stable : fullSyncOrbitN 37 = fullSynchronizedGraph := by
  native_decide


def fullSynchronizedMatrices : Finset Mat5 := fullSynchronizedGraph.image Prod.fst

def generatedPointTables : Finset PointTable := fullSynchronizedGraph.image Prod.snd

 theorem full_synchronized_matrices_eq_generated_e6 :
    fullSynchronizedMatrices = generatedMatrixSet := by
  native_decide

 theorem generated_point_table_card : generatedPointTables.card = 51840 := by
  native_decide

/-- The synchronized graph is functional in both directions: this is the exact
same-action identification of the two generated finite images. -/
theorem full_matrix_determines_point_table :
    ∀ a b, a ∈ fullSynchronizedGraph → b ∈ fullSynchronizedGraph →
      a.1 = b.1 → a.2 = b.2 := by
  native_decide

 theorem full_point_table_determines_matrix :
    ∀ a b, a ∈ fullSynchronizedGraph → b ∈ fullSynchronizedGraph →
      a.2 = b.2 → a.1 = b.1 := by
  native_decide

 theorem every_generated_matrix_has_unique_point_table :
    ∀ M, M ∈ generatedMatrixSet →
      ∃! P, P ∈ generatedPointTables ∧ (M,P) ∈ fullSynchronizedGraph := by
  native_decide

 theorem every_generated_point_table_has_unique_matrix :
    ∀ P, P ∈ generatedPointTables →
      ∃! M, M ∈ generatedMatrixSet ∧ (M,P) ∈ fullSynchronizedGraph := by
  native_decide

/-- Generator pairs themselves occur literally in the global graph. -/
theorem every_simple_generator_pair_occurs :
    ∀ s, (generatorMatrix s, generatorPointTable s) ∈ fullSynchronizedGraph := by
  native_decide

structure Boundary where
  rawTernary27NumberingPaid : Bool
  sixGlobalPointTablesTyped : Bool
  generatorMinusculeIntertwiningPaid : Bool
  generatorSchlafliPreservationPaid : Bool
  fullPairedClosure51840Paid : Bool
  matrixProjectionEqualsGeneratedE6Paid : Bool
  pointPermutationImageFaithful51840Paid : Bool
  fullSameActionGraphBijectiveBothWaysPaid : Bool
  directA5LocalCheckRetained : Bool
  albertProductPaid : Bool
  monsterNormalizerRealizationPaid : Bool
  deriving Repr


def canonicalBoundary : Boundary where
  rawTernary27NumberingPaid := true
  sixGlobalPointTablesTyped := true
  generatorMinusculeIntertwiningPaid := true
  generatorSchlafliPreservationPaid := true
  fullPairedClosure51840Paid := true
  matrixProjectionEqualsGeneratedE6Paid := true
  pointPermutationImageFaithful51840Paid := true
  fullSameActionGraphBijectiveBothWaysPaid := true
  directA5LocalCheckRetained := true
  albertProductPaid := false
  monsterNormalizerRealizationPaid := false

end Integration.E6FullMatrixTernary27SameAction
