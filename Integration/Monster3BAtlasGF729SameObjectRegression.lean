import Integration.Monster3BAtlasGF729SameObject
import Mathlib

/-!
Regression contract for the explicit Monster-3B ATLAS X6-compression -> selected
GF(729) same-object weld.  The production owner must prove the literal 6x6
intertwiner and its two-sided inverse over F3; executable irreducibility remains
separately attributed to the companion exact producer.
-/

namespace Integration.Monster3BAtlasGF729SameObjectRegression

open Integration.Monster3BAtlasGF729SameObject

example : intertwinerQ * compressionT = selectedMulBeta * intertwinerQ :=
  compression_selected_action_intertwines

example : intertwinerQInv * intertwinerQ = 1 :=
  intertwiner_left_inverse

example : intertwinerQ * intertwinerQInv = 1 :=
  intertwiner_right_inverse

example : canonicalBoundary.explicitCompressionMatrixPaid = true := by decide
example : canonicalBoundary.explicitGF729ActionMatrixPaid = true := by decide
example : canonicalBoundary.explicitInvertibleIntertwinerPaid = true := by decide
example : canonicalBoundary.sameSelectedGF729ActionPaid = true := by decide
example : canonicalBoundary.fullMonsterOrbitSemanticsPaid = false := by decide

end Integration.Monster3BAtlasGF729SameObjectRegression
