import Synthesis.RiemannG21ScaledTanhMonotonicity

open Set

namespace Synthesis

example : StrictMonoOn scaledTanhCarrier (Ioi 0) := by
  exact scaledTanhCarrier_strictMonoOn

end Synthesis
