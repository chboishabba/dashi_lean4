import Synthesis.LinearConsumerSyntheticBidiBaselineActionBytes

/-!
Regression for the canonical one-byte-per-row serialization of the fully
concrete Lean baseline action.
-/

namespace Synthesis

example : SyntheticBidiRows → BitVec 8 := syntheticBidiBaselineActionRowByte
example : Fin 924 → BitVec 8 := syntheticBidiBaselineActionBytes

example (r : SyntheticBidiRows) :
    syntheticBidiBaselineActionBytes r = syntheticBidiBaselineActionRowByte r :=
  syntheticBidiBaselineActionBytes_apply r

end Synthesis
