import Integration.Monster3BAtlasGF729SameObject
import Mathlib

/-!
Regression contract for the preferred primitive Monster-3B ATLAS X6
compression -> selected GF(729) same-object weld.  The production owner proves
the literal 6x6 intertwiner and its two-sided inverse over F3.  Primitive order,
punctured orbit and stabilizer remain explicitly attributed to the companion
exact producer until separately replayed in Lean.
-/

namespace Integration.Monster3BAtlasGF729SameObjectRegression

open Integration.Monster3BAtlasGF729SameObject

example : intertwinerQ * compressionT = selectedMulGamma * intertwinerQ :=
  compression_selected_action_intertwines

example : intertwinerQInv * intertwinerQ = 1 :=
  intertwiner_left_inverse

example : intertwinerQ * intertwinerQInv = 1 :=
  intertwiner_right_inverse

example : canonicalBoundary.explicitCompressionMatrixPaid = true := by decide
example : canonicalBoundary.explicitGF729ActionMatrixPaid = true := by decide
example : canonicalBoundary.explicitInvertibleIntertwinerPaid = true := by decide
example : canonicalBoundary.sameSelectedGF729ActionPaid = true := by decide
example : canonicalBoundary.primitiveOrder728PaidByExactProducer = true := by decide
example : canonicalBoundary.puncturedOrbit728PaidByExactProducer = true := by decide
example : canonicalBoundary.puncturedStabilizerTrivialPaidByExactProducer = true := by decide
example : canonicalBoundary.primitiveOrderReprovedInLeanHere = false := by decide
example : canonicalBoundary.fullMonsterOrbitSemanticsPaid = false := by decide

end Integration.Monster3BAtlasGF729SameObjectRegression
