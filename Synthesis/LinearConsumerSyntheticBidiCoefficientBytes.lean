import Synthesis.LinearConsumerSyntheticBidiCoefficients

/-!
# Canonical coefficient-byte bridge

The dashiRTX baseline producer serializes every recovered 8x8 GF(2)
coefficient layer as eight row bytes, row-major, with bit `c` equal to matrix
entry `(r,c)`.  This file exposes exactly the same finite representation for
the Lean fixture.

No hash implementation or production CADO identity is introduced here.  The
purpose is only to put the runtime and Lean fixtures on one common 136-byte
carrier so their same-object payment can be made by finite equality.
-/

namespace Synthesis

/-- Row `r` of recovered layer `i`, packed with column `c` at bit `c`. -/
def syntheticBidiRecoveredCoefficientRowByte
    (i : Fin 17) (r : Fin 8) : BitVec 8 :=
  BitVec.ofNat 8
    ((syntheticBidiRecoveredCoefficientWord i).toNat / 2 ^ (r.val * 8))

/-- The row-major 17 * 8 = 136 byte serialization used by the runtime producer. -/
def syntheticBidiRecoveredCoefficientBytes (n : Fin 136) : BitVec 8 :=
  syntheticBidiRecoveredCoefficientRowByte
    ⟨n.val / 8, by omega⟩
    ⟨n.val % 8, Nat.mod_lt _ (by omega)⟩

@[simp]
theorem syntheticBidiRecoveredCoefficientBytes_apply
    (i : Fin 17) (r : Fin 8) :
    syntheticBidiRecoveredCoefficientBytes ⟨i.val * 8 + r.val, by omega⟩ =
      syntheticBidiRecoveredCoefficientRowByte i r := by
  unfold syntheticBidiRecoveredCoefficientBytes
  congr
  · apply Fin.ext
    simp
  · apply Fin.ext
    simp

end Synthesis
