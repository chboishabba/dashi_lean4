import Synthesis.LinearConsumerSyntheticBidiCoefficients

/-!
Regression surface for the exact 17-layer coefficient family recovered by the
hash-bound dashiRTX baseline producer.

The production module must expose the runtime row-major 64-bit layer words as a
`Fin 17 -> 8x8` GF(2) matrix family.  This is a finite fixture only; it does not
identify the fixture with production CADO `F.sols*` data.
-/

namespace Synthesis

example : Fin 17 → Matrix SyntheticBidiBlock SyntheticBidiBlock (ZMod 2) :=
  syntheticBidiRecoveredCoefficientFamily

example : syntheticBidiRecoveredCoefficientWord 0 =
    syntheticBidiWordOfNat 0x0000000000000000 := by
  rfl

example : syntheticBidiRecoveredCoefficientWord 1 =
    syntheticBidiWordOfNat 0x4848484848004848 := by
  rfl

example : syntheticBidiRecoveredCoefficientWord 16 =
    syntheticBidiWordOfNat 0x0000000000000053 := by
  rfl

example (i : Fin 17) (r c : SyntheticBidiBlock) :
    syntheticBidiRecoveredCoefficientFamily i r c =
      if (syntheticBidiRecoveredCoefficientWord i).getLsbD (r.val * 8 + c.val)
      then 1
      else 0 :=
  syntheticBidiRecoveredCoefficientFamily_apply i r c

end Synthesis
