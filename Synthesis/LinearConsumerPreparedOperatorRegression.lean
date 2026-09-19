import Synthesis.LinearConsumerPreparedOperator

/-!
Regression surface for the baseline synthetic prepared-operator bridge.

For the identity-permutation runtime context, the executable operator is

    Y |-> A * (Aᵀ * Y).

The production module must expose this as a linear endomorphism through the
already-owned fixed-left matrix action, and prove the associative equality with
left multiplication by `A * A.transpose`.
-/

namespace Synthesis

universe uR uC uB

example {rows : Type uR} {cols : Type uC} {block : Type uB}
    [Fintype rows] [Fintype cols]
    (A : Matrix rows cols (ZMod 2)) :
    Matrix rows block (ZMod 2) →ₗ[ZMod 2] Matrix rows block (ZMod 2) :=
  gramPreparedOperator A

example {rows : Type uR} {cols : Type uC} {block : Type uB}
    [Fintype rows] [Fintype cols]
    (A : Matrix rows cols (ZMod 2))
    (Y : Matrix rows block (ZMod 2)) :
    gramPreparedOperator A Y = A * (A.transpose * Y) :=
  gramPreparedOperator_apply A Y

end Synthesis
