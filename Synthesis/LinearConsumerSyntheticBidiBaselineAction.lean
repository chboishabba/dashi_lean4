import Synthesis.LinearConsumerKrylovFamilyAction
import Synthesis.LinearConsumerSyntheticBidiCoefficients

/-!
# Fully assembled formal synthetic bidi baseline action

The formal side now owns all three finite baseline inputs used by the synthetic
runtime action:

* the 924x512 incidence constructor `syntheticBidiIncidence`;
* the 924x8 deterministic seed block `syntheticBidiSeedBlock`;
* the recovered 17-layer 8x8 coefficient family
  `syntheticBidiRecoveredCoefficientFamily`.

Using the generic Krylov-action donor therefore gives a single formal baseline
linear action map and its evaluated output.  This source does not by itself
prove that the runtime constructors/bytes are the same Lean objects; those
cross-language transports remain separate obligations.
-/

namespace Synthesis

open scoped BigOperators

/-- Linear coefficient-family action for the exact formal synthetic baseline. -/
def syntheticBidiBaselineActionMap :
    (Fin 17 → Matrix SyntheticBidiBlock SyntheticBidiBlock (ZMod 2)) →ₗ[ZMod 2]
      Matrix SyntheticBidiRows SyntheticBidiBlock (ZMod 2) :=
  krylovCoefficientFamilyAction
    syntheticBidiPreparedOperator
    syntheticBidiSeedBlock

/-- Formal action output on the exact recovered degree-17 coefficient fixture. -/
def syntheticBidiBaselineAction :
    Matrix SyntheticBidiRows SyntheticBidiBlock (ZMod 2) :=
  syntheticBidiBaselineActionMap syntheticBidiRecoveredCoefficientFamily

@[simp]
theorem syntheticBidiBaselineAction_eq_krylov_sum :
    syntheticBidiBaselineAction =
      ∑ i : Fin 17,
        ((syntheticBidiPreparedOperator ^ (i : Nat)) syntheticBidiSeedBlock) *
          syntheticBidiRecoveredCoefficientFamily i :=
  rfl

end Synthesis
