import Integration.Monster3BAtlasGF729SameObject
import Mathlib

/-!
Regression contract for the preferred primitive Monster-3B ATLAS X6
compression -> selected GF(729) same-object weld.  The production owner proves
the literal 6x6 intertwiner and inverse, then replays the finite primitive action
on the same six-dimensional F3 carrier.
-/

namespace Integration.Monster3BAtlasGF729SameObjectRegression

open Integration.Monster3BAtlasGF729SameObject

example : intertwinerQ * compressionT = selectedMulGamma * intertwinerQ :=
  compression_selected_action_intertwines

example : intertwinerQInv * intertwinerQ = 1 := intertwiner_left_inverse
example : intertwinerQ * intertwinerQInv = 1 := intertwiner_right_inverse

example : selectedMulGamma ^ 728 = 1 := selected_mul_gamma_pow_728
example : ∀ n : Fin 727, selectedMulGamma ^ (n.1 + 1) ≠ 1 :=
  selected_mul_gamma_no_positive_power_below_728
example : primitiveOrbit.card = 728 := primitive_orbit_card
example : canonicalSeedStabilizer.card = 1 := canonical_seed_stabilizer_card

example : canonicalBoundary.explicitCompressionMatrixPaid = true := by decide
example : canonicalBoundary.explicitGF729ActionMatrixPaid = true := by decide
example : canonicalBoundary.explicitInvertibleIntertwinerPaid = true := by decide
example : canonicalBoundary.sameSelectedGF729ActionPaid = true := by decide
example : canonicalBoundary.primitiveOrderReprovedInLeanHere = true := by decide
example : canonicalBoundary.puncturedOrbit728ReprovedInLeanHere = true := by decide
example : canonicalBoundary.puncturedStabilizerTrivialReprovedInLeanHere = true := by decide
example : canonicalBoundary.fullMonsterOrbitSemanticsPaid = false := by decide

end Integration.Monster3BAtlasGF729SameObjectRegression
