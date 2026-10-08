import Integration.E8TernaryBranchingActionObstruction

namespace Integration.E8TernaryBranchingActionObstructionRegression

open Integration.E8TernaryBranchingActionObstruction

example : ∀ s, actMixedA s mixedAZero = mixedAZero := mixed_a_zero_fixed
example : ∀ r : LiteralMixedPlus, ¬ LiteralFixedByAllE6 r.1 :=
  no_literal_mixed_plus_global_fixed_point
example : ∀ r : LiteralMixedMinus, ¬ LiteralFixedByAllE6 r.1 :=
  no_literal_mixed_minus_global_fixed_point
example : ¬ MixedAPlusSameActionRecognition := mixed_a_plus_same_action_impossible
example : ¬ MixedAMinusSameActionRecognition := mixed_a_minus_same_action_impossible
example : ¬ MixedBInvariantUnderE6 := mixed_b_not_e6_invariant
example : ¬ A2SectorInvariantUnderE6 := a2_sector_not_e6_invariant
example : canonicalBoundary.countMatchedBranchingSameActionBlocked = true := rfl
example : canonicalBoundary.cardinalityBranchingStillValid = true := rfl

end Integration.E8TernaryBranchingActionObstructionRegression
