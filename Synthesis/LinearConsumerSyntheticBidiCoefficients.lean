import Synthesis.LinearConsumerSyntheticBidiSeed

/-!
# Exact recovered synthetic bidi coefficient family

Finite mirror of the 17 coefficient layers recovered by the hash-bound
`dashiRTX` baseline producer.

Each runtime 8x8 GF(2) layer is encoded row-major into one 64-bit word: bit
`8*r + c` is matrix entry `(r,c)`.  The listed words were extracted from the
committed runtime producer whose coefficient-family digest is recorded on the
Agda side.

This file owns only that finite formal fixture.  It does not prove the fixture
has the runtime digest, does not identify it with historical/production CADO
`F.sols*`, and does not claim an RSA-260 same-object artifact.
-/

namespace Synthesis

/-- Row-major 64-bit coefficient-layer words for the deterministic degree-17
baseline generator. -/
def syntheticBidiRecoveredCoefficientWord (i : Fin 17) : SyntheticBidiWord :=
  syntheticBidiWordOfNat <| match i.val with
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

/-- Exact finite 17x8x8 GF(2) coefficient-family fixture. -/
def syntheticBidiRecoveredCoefficientFamily :
    Fin 17 → Matrix SyntheticBidiBlock SyntheticBidiBlock (ZMod 2) :=
  fun i r c =>
    if (syntheticBidiRecoveredCoefficientWord i).getLsbD (r.val * 8 + c.val)
    then 1
    else 0

@[simp]
theorem syntheticBidiRecoveredCoefficientFamily_apply
    (i : Fin 17) (r c : SyntheticBidiBlock) :
    syntheticBidiRecoveredCoefficientFamily i r c =
      if (syntheticBidiRecoveredCoefficientWord i).getLsbD (r.val * 8 + c.val)
      then 1
      else 0 :=
  rfl

end Synthesis
