import Synthesis.LinearConsumerSyntheticBidiSeedBytes

/-!
Regression for the canonical one-byte-per-row serialization of the deterministic
924x8 baseline seed block V.
-/

namespace Synthesis

example : SyntheticBidiRows → BitVec 8 := syntheticBidiSeedRowByte
example : Fin 924 → BitVec 8 := syntheticBidiSeedBytes

example (r : SyntheticBidiRows) :
    syntheticBidiSeedBytes r = syntheticBidiSeedRowByte r :=
  syntheticBidiSeedBytes_apply r

end Synthesis
