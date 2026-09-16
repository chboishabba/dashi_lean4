import Synthesis.LinearConsumerKrylovFamilyAction

/-!
Regression surface for the Krylov-specialized matrix-family action.

The production module must expose the exact generic shape

    F |-> sum_i (M^i V) * F_i

for an abstract linear endomorphism `M` on the Krylov-block carrier and a
seed block `V`.  This is still domain-neutral and does not identify `M` or `V`
with the synthetic/runtime/CADO objects.
-/

namespace Synthesis

open scoped BigOperators

universe uL uM uN

example {d : Nat} {l : Type uL} {m : Type uM} {n : Type uN}
    [Fintype m]
    (M : Module.End (ZMod 2) (Matrix l m (ZMod 2)))
    (V : Matrix l m (ZMod 2)) :
    (Fin d → Matrix m n (ZMod 2)) →ₗ[ZMod 2] Matrix l n (ZMod 2) :=
  krylovCoefficientFamilyAction M V

example {d : Nat} {l : Type uL} {m : Type uM} {n : Type uN}
    [Fintype m]
    (M : Module.End (ZMod 2) (Matrix l m (ZMod 2)))
    (V : Matrix l m (ZMod 2))
    (F : Fin d → Matrix m n (ZMod 2)) :
    krylovCoefficientFamilyAction M V F =
      ∑ i, ((M ^ (i : Nat)) V) * F i :=
  krylovCoefficientFamilyAction_apply M V F

end Synthesis
