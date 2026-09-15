import Synthesis.LinearConsumerFiniteFamilyAction
import Mathlib.LinearAlgebra.Matrix.Bilinear
import Mathlib.Data.ZMod.Basic

/-!
# Matrix-family linear consumer action

A thin generic donor for the RSA bidi consumer-family lane.

For fixed matrices `K i`, the coefficient-layer action

    F i |-> K i * F i

is already linear by mathlib's `Matrix.mulLeftLinearMap`.  Combining those
layer maps with `finiteFamilyAction` gives the exact finite-family shape used by
the synthetic Block-Wiedemann/mksol-style action:

    F |-> sum_i K i * F i.

This file is still domain-neutral.  It does not identify `K i` with a CADO
Krylov block, choose a generator degree, bind a production matrix/operator, or
turn a runtime rank calculation into a formal joint-kernel certificate.
-/

namespace Synthesis

open scoped BigOperators

universe uI uM uN

/-- For a fixed left matrix over `GF(2)`, right-matrix multiplication is a
linear map in the coefficient matrix. -/
def matrixLayerAction {m : Type uM} {n : Type uN}
    [Fintype m] (K : Matrix m m (ZMod 2)) :
    Matrix m n (ZMod 2) →ₗ[ZMod 2] Matrix m n (ZMod 2) :=
  Matrix.mulLeftLinearMap n (ZMod 2) K

@[simp]
theorem matrixLayerAction_apply {m : Type uM} {n : Type uN}
    [Fintype m] (K : Matrix m m (ZMod 2)) (F : Matrix m n (ZMod 2)) :
    matrixLayerAction K F = K * F :=
  rfl

/-- Sum a finite family of fixed-left matrix actions. -/
def matrixCoefficientFamilyAction {ι : Type uI} {m : Type uM} {n : Type uN}
    [Fintype ι] [Fintype m]
    (K : ι → Matrix m m (ZMod 2)) :
    (ι → Matrix m n (ZMod 2)) →ₗ[ZMod 2] Matrix m n (ZMod 2) :=
  finiteFamilyAction (fun i => matrixLayerAction (K i))

@[simp]
theorem matrixCoefficientFamilyAction_apply
    {ι : Type uI} {m : Type uM} {n : Type uN}
    [Fintype ι] [Fintype m]
    (K : ι → Matrix m m (ZMod 2))
    (F : ι → Matrix m n (ZMod 2)) :
    matrixCoefficientFamilyAction K F = ∑ i, K i * F i :=
  rfl

end Synthesis
