import Integration.Monster3BAtlasGF729SameObject
import Mathlib

/-!
Regression contract for the preferred center-preserving primitive Monster-3B
ATLAS X6 compression -> selected GF(729) same-object weld.  The theorem
statements are source-written in Lean; exact-head kernel observation remains a
separate status flag because Lean is unavailable in the current execution
environment.
-/

namespace Integration.Monster3BAtlasGF729SameObjectRegression

open Integration.Monster3BAtlasGF729SameObject

example : intertwinerQ * compressionT = selectedMulDelta * intertwinerQ :=
  compression_selected_action_intertwines
example : intertwinerQInv * intertwinerQ = 1 := intertwiner_left_inverse
example : intertwinerQ * intertwinerQInv = 1 := intertwiner_right_inverse
example : selectedMulDelta ^ 728 = 1 := selected_mul_delta_pow_728
example : ∀ n : Fin 727, selectedMulDelta ^ (n.1 + 1) ≠ 1 :=
  selected_mul_delta_no_positive_power_below_728
example : primitiveOrbit.card = 728 := primitive_orbit_card
example : canonicalSeedStabilizer.card = 1 := canonical_seed_stabilizer_card

example : canonicalBoundary.centerPreservingPrimitiveSourceWordPaidByExactProducer = true := by decide
example : canonicalBoundary.explicitCompressionMatrixPaid = true := by decide
example : canonicalBoundary.explicitGF729ActionMatrixPaid = true := by decide
example : canonicalBoundary.explicitInvertibleIntertwinerPaid = true := by decide
example : canonicalBoundary.sameSelectedGF729ActionSourceWritten = true := by decide
example : canonicalBoundary.primitiveOrder728LeanSourceWritten = true := by decide
example : canonicalBoundary.puncturedOrbit728LeanSourceWritten = true := by decide
example : canonicalBoundary.puncturedStabilizerTrivialLeanSourceWritten = true := by decide
example : canonicalBoundary.leanExactHeadKernelReceiptObserved = false := by decide
example : canonicalBoundary.fullMonsterSemanticActionRecognitionPaid = false := by decide

end Integration.Monster3BAtlasGF729SameObjectRegression
