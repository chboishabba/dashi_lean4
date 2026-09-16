import Mathlib.Tactic
import Synthesis.LinearConsumerSyntheticBidiCoefficientBytes

/-!
# Exact runtime/formal coefficient-byte equality

The dashiRTX baseline execution recovered 17 GF(2) coefficient layers.  This
module records those runtime layers independently as the 17 row-major 64-bit
words emitted by the executable recovery and compares their canonical 136-byte
serialization with the formal Lean coefficient fixture.

This pays only the synthetic recovered-coefficient identity.  It does not
identify historical/production CADO `F.sols*`, does not pay the seed/operator
identity, and does not transport the runtime action or joint-kernel receipt.
-/

namespace Synthesis

/-- Runtime-recovered row-major 64-bit words from the hash-bound baseline run. -/
def syntheticBidiRuntimeRecoveredCoefficientWord (i : Fin 17) : BitVec 64 :=
  BitVec.ofNat 64 <| match i.val with
    | 0  => 0x0000000000000000
    | 1  => 0x4848484848004848
    | 2  => 0xBA56B99119685E8D
    | 3  => 0x2F40C3D97B12CF9E
    | 4  => 0xFC7F8209F1079D14
    | 5  => 0xF70F2FEB547CC774
    | 6  => 0x23245B65E4C7863E
    | 7  => 0x8284D169ED034976
    | 8  => 0xE840899D90937AA7
    | 9  => 0x23C049F9796960AA
    | 10 => 0x9EE4D6757120F63B
    | 11 => 0x9AA601DB5E904FC9
    | 12 => 0xE76E1F0AA90C6A2B
    | 13 => 0xB1363F03717EE740
    | 14 => 0xAD82657D5CF422A9
    | 15 => 0x0000DA6A14A43D21
    | 16 => 0x0000000000000053
    | _  => 0

/-- Runtime row byte `r` of recovered layer `i`. -/
def syntheticBidiRuntimeRecoveredCoefficientRowByte
    (i : Fin 17) (r : Fin 8) : BitVec 8 :=
  BitVec.ofNat 8
    ((syntheticBidiRuntimeRecoveredCoefficientWord i).toNat / 2 ^ (r.val * 8))

/-- Exact 136-byte runtime carrier: 17 layers × 8 row bytes. -/
def syntheticBidiRuntimeRecoveredCoefficientBytes (n : Fin 136) : BitVec 8 :=
  syntheticBidiRuntimeRecoveredCoefficientRowByte
    ⟨n.val / 8, by omega⟩
    ⟨n.val % 8, Nat.mod_lt _ (by omega)⟩

/-- The independently recorded runtime words are exactly the formal Lean words. -/
theorem syntheticBidiRuntimeRecoveredCoefficientWord_eq_formal :
    syntheticBidiRuntimeRecoveredCoefficientWord =
      syntheticBidiRecoveredCoefficientWord := by
  funext i
  fin_cases i <;> rfl

/-- Hence the canonical 136 runtime bytes and formal bytes are identical. -/
theorem syntheticBidiRuntimeRecoveredCoefficientBytes_eq_formal :
    syntheticBidiRuntimeRecoveredCoefficientBytes =
      syntheticBidiRecoveredCoefficientBytes := by
  funext n
  unfold syntheticBidiRuntimeRecoveredCoefficientBytes
  unfold syntheticBidiRecoveredCoefficientBytes
  rw [syntheticBidiRuntimeRecoveredCoefficientWord_eq_formal]

end Synthesis
