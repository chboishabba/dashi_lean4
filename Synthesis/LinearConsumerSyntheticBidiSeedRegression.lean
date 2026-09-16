import Synthesis.LinearConsumerSyntheticBidiSeed

/-!
Regression surface for the exact deterministic 924x8 baseline seed block used
by the synthetic bidi runtime.
-/

namespace Synthesis

example : Matrix (Fin 924) (Fin 8) (ZMod 2) :=
  syntheticBidiSeedBlock

example (r : Fin 924) (j : Fin 8) :
    syntheticBidiSeedBlock r j =
      if (syntheticBidiSeedWord j (r.val / 64)).getLsbD (r.val % 64)
      then 1
      else 0 :=
  syntheticBidiSeedBlock_apply r j

end Synthesis
