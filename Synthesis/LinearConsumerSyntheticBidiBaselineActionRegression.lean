import Synthesis.LinearConsumerSyntheticBidiBaselineAction

/-!
Regression surface for the formal baseline synthetic action assembled from the
explicit incidence constructor, explicit seed constructor, and exact recovered
17-layer coefficient fixture.
-/

namespace Synthesis

example :
    (Fin 17 → Matrix SyntheticBidiBlock SyntheticBidiBlock (ZMod 2)) →ₗ[ZMod 2]
      Matrix SyntheticBidiRows SyntheticBidiBlock (ZMod 2) :=
  syntheticBidiBaselineActionMap

example : Matrix SyntheticBidiRows SyntheticBidiBlock (ZMod 2) :=
  syntheticBidiBaselineAction

example :
    syntheticBidiBaselineAction =
      ∑ i : Fin 17,
        ((syntheticBidiPreparedOperator ^ (i : Nat)) syntheticBidiSeedBlock) *
          syntheticBidiRecoveredCoefficientFamily i :=
  syntheticBidiBaselineAction_eq_krylov_sum

end Synthesis
