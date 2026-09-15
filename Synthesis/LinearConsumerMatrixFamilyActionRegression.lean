import Synthesis.LinearConsumerMatrixFamilyAction

/-!
Regression surface for the matrix-family action donor.

The production module must expose a per-layer fixed-left-multiplication linear
map and the finite-family action obtained by summing those layer maps.
-/

namespace Synthesis

open scoped BigOperators

universe uI uM uN

example {ι : Type uI} {m : Type uM} {n : Type uN}
    [Fintype ι] [Fintype m]
    (K : ι → Matrix m m (ZMod 2)) :
    (ι → Matrix m n (ZMod 2)) →ₗ[ZMod 2] Matrix m n (ZMod 2) :=
  matrixCoefficientFamilyAction K

example {ι : Type uI} {m : Type uM} {n : Type uN}
    [Fintype ι] [Fintype m]
    (K : ι → Matrix m m (ZMod 2))
    (F : ι → Matrix m n (ZMod 2)) :
    matrixCoefficientFamilyAction K F = ∑ i, K i * F i :=
  matrixCoefficientFamilyAction_apply K F

end Synthesis
