import Synthesis.LinearConsumerSyntheticBidiRuntimeByteEquality

namespace Synthesis

example : syntheticBidiRuntimeSeedBytes = syntheticBidiSeedBytes :=
  syntheticBidiRuntimeSeedBytes_eq_formal

example : syntheticBidiRuntimeActionBytes = syntheticBidiBaselineActionBytes :=
  syntheticBidiRuntimeActionBytes_eq_formal

end Synthesis
