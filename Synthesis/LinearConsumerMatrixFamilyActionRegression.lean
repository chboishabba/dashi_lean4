import Synthesis.LinearConsumerMatrixFamilyAction

/-!
Regression surface for the matrix-family action donor.

The production module must expose heterogeneous fixed-left multiplication:

    K : l x m,   F : m x n,   K * F : l x n.

This matches the synthetic mksol-style shape where the Krylov block is
ROWS x BLOCK and the generator coefficient is BLOCK x BLOCK.  The previous
square-only regression was too narrow for that carrier.
-/

namespace Synthesis

open scoped BigOperators

universe uI uL uM uN

example {ι : Type uI} {l : Type uL} {m : Type uM} {n : Type uN}
    [Fintype ι] [Fintype m]
    (K : ι → Matrix l m (ZMod 2)) :
    (ι → Matrix m n (ZMod 2)) →ₗ[ZMod 2] Matrix l n (ZMod 2) :=
  matrixCoefficientFamilyAction K

example {ι : Type uI} {l : Type uL} {m : Type uM} {n : Type uN}
    [Fintype ι] [Fintype m]
    (K : ι → Matrix l m (ZMod 2))
    (F : ι → Matrix m n (ZMod 2)) :
    matrixCoefficientFamilyAction K F = ∑ i, K i * F i :=
  matrixCoefficientFamilyAction_apply K F

end Synthesis
