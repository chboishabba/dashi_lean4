import Integration.E6FullMatrixTernary27SameAction
import Mathlib

/-!
# Coxeter coherence of the full raw ternary-27 E6 action

The preceding owner gives six explicit generator permutations on the same raw
ternary 27 and synchronizes their complete finite closure with the 51,840 matrix
image.  This file pays the presentation-level path-independence receipts:

* every simple generator is an involution;
* adjacent generators satisfy the E6 length-three braid relation;
* distinct non-adjacent generators commute.

Thus the raw ternary generator action satisfies the same E6 Coxeter presentation
as the independently-paid mod-3 matrix action.  Together with the 51,840
synchronized faithful closure, this is the global finite same-action theorem.
-/

namespace Integration.E6Ternary27CoxeterAction

open Integration.E6Mod3WeylAction
open Integration.E6FullMatrixTernary27SameAction
open Integration.Ternary27HyperformSchlafliRecognition

/-- Generator involutions on all 27 raw ternary points. -/
theorem raw_ternary_simple_generators_involutive :
    ∀ s p, globalGeneratorActPoint s (globalGeneratorActPoint s p) = p := by
  native_decide

/-- Adjacent E6 generators satisfy the braid relation on the raw ternary carrier. -/
theorem raw_ternary_adjacent_braid :
    ∀ i j,
      coxeterAdjacent i j = true →
      ∀ p,
        globalGeneratorActPoint i
          (globalGeneratorActPoint j (globalGeneratorActPoint i p)) =
        globalGeneratorActPoint j
          (globalGeneratorActPoint i (globalGeneratorActPoint j p)) := by
  native_decide

/-- Distinct non-adjacent E6 generators commute on the raw ternary carrier. -/
theorem raw_ternary_nonadjacent_commute :
    ∀ i j,
      i ≠ j → coxeterAdjacent i j = false →
      ∀ p,
        globalGeneratorActPoint i (globalGeneratorActPoint j p) =
        globalGeneratorActPoint j (globalGeneratorActPoint i p) := by
  native_decide

/-- The same presentation is seen at the 27-index table level. -/
theorem point_table_simple_generators_involutive :
    ∀ s i, generatorPointTable s (generatorPointTable s i) = i := by
  native_decide

theorem point_table_adjacent_braid :
    ∀ a b,
      coxeterAdjacent a b = true →
      pointTableComp (generatorPointTable a)
          (pointTableComp (generatorPointTable b) (generatorPointTable a)) =
      pointTableComp (generatorPointTable b)
          (pointTableComp (generatorPointTable a) (generatorPointTable b)) := by
  native_decide

theorem point_table_nonadjacent_commute :
    ∀ a b,
      a ≠ b → coxeterAdjacent a b = false →
      pointTableComp (generatorPointTable a) (generatorPointTable b) =
      pointTableComp (generatorPointTable b) (generatorPointTable a) := by
  native_decide

structure Boundary where
  rawTernaryGeneratorInvolutionsPaid : Bool
  rawTernaryAdjacentBraidPaid : Bool
  rawTernaryNonadjacentCommutationPaid : Bool
  pointTableCoxeterPresentationPaid : Bool
  synchronizedFaithfulClosureConsumed : Bool
  globalFiniteE6SameActionPaid : Bool
  monsterNormalizerPhysicalRealizationPaid : Bool
  albertJordanStructurePaid : Bool
  deriving Repr


def canonicalBoundary : Boundary where
  rawTernaryGeneratorInvolutionsPaid := true
  rawTernaryAdjacentBraidPaid := true
  rawTernaryNonadjacentCommutationPaid := true
  pointTableCoxeterPresentationPaid := true
  synchronizedFaithfulClosureConsumed := true
  globalFiniteE6SameActionPaid := true
  monsterNormalizerPhysicalRealizationPaid := false
  albertJordanStructurePaid := false

end Integration.E6Ternary27CoxeterAction
