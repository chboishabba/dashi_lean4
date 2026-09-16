import Synthesis.LinearConsumerMatrixFamilyAction

/-!
# Prepared operator for the identity-permutation bidi runtime context

The synthetic runtime baseline uses

    apply_B(Y) = A * (A.transpose * Y)

over GF(2), with the middle-coordinate permutation equal to the identity.

This file owns only the generic algebraic bridge: left multiplication by the
Gram-style matrix `A * A.transpose` is the same action by associativity.  It
does not identify any concrete runtime matrix with `A`, does not bind a runtime
hash, and does not claim CADO or production RSA-260 semantics.
-/

namespace Synthesis

universe uR uC uB

/-- The linear prepared operator induced by a rectangular GF(2) matrix `A` in
the identity-permutation context. -/
def gramPreparedOperator {rows : Type uR} {cols : Type uC} {block : Type uB}
    [Fintype rows] [Fintype cols]
    (A : Matrix rows cols (ZMod 2)) :
    Matrix rows block (ZMod 2) →ₗ[ZMod 2] Matrix rows block (ZMod 2) :=
  matrixLayerAction (A * A.transpose)

@[simp]
theorem gramPreparedOperator_apply
    {rows : Type uR} {cols : Type uC} {block : Type uB}
    [Fintype rows] [Fintype cols]
    (A : Matrix rows cols (ZMod 2))
    (Y : Matrix rows block (ZMod 2)) :
    gramPreparedOperator A Y = A * (A.transpose * Y) := by
  simp [gramPreparedOperator, Matrix.mul_assoc]

end Synthesis
