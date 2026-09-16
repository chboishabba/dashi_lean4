import Synthesis.LinearConsumerSyntheticBidiIncidence

/-!
Regression surface for the exact finite synthetic incidence constructor mirrored
from the dashiRTX baseline runtime.
-/

namespace Synthesis

example : Matrix (Fin 924) (Fin 512) (ZMod 2) :=
  syntheticBidiIncidence

example :
    Matrix (Fin 924) (Fin 8) (ZMod 2) →ₗ[ZMod 2]
      Matrix (Fin 924) (Fin 8) (ZMod 2) :=
  syntheticBidiPreparedOperator

example (Y : Matrix (Fin 924) (Fin 8) (ZMod 2)) :
    syntheticBidiPreparedOperator Y =
      syntheticBidiIncidence * (syntheticBidiIncidence.transpose * Y) :=
  syntheticBidiPreparedOperator_apply Y

end Synthesis
