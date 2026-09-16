import Synthesis.LinearConsumerSyntheticBidiCoefficientBytes

/-!
Regression for the common runtime/Lean byte representation of the recovered
17-layer synthetic coefficient family.

The production module must expose the row-major byte at `(layer,row)`, and the
flattened 136-byte fixture. This is a representation bridge only; it does not
claim production CADO identity.
-/

namespace Synthesis

example : Fin 17 → Fin 8 → BitVec 8 := syntheticBidiRecoveredCoefficientRowByte

example : Fin 136 → BitVec 8 := syntheticBidiRecoveredCoefficientBytes

example : syntheticBidiRecoveredCoefficientRowByte 1 0 = 0x48#8 := by rfl
example : syntheticBidiRecoveredCoefficientRowByte 1 2 = 0x00#8 := by rfl
example : syntheticBidiRecoveredCoefficientRowByte 16 0 = 0x53#8 := by rfl
example : syntheticBidiRecoveredCoefficientRowByte 16 7 = 0x00#8 := by rfl

example (i : Fin 17) (r : Fin 8) :
    syntheticBidiRecoveredCoefficientBytes ⟨i.val * 8 + r.val, by omega⟩ =
      syntheticBidiRecoveredCoefficientRowByte i r :=
  syntheticBidiRecoveredCoefficientBytes_apply i r

end Synthesis
