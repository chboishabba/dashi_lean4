import Synthesis.LinearConsumerSyntheticBidiTwoVJointKernelCertificate

/-!
# Regression for the finite two-V synthetic bidi certificate

This target must remain thin: the production owner reconstructs the two formal
Krylov consumers from the existing prepared operator and deterministic seeds,
checks the producer-certified finite inverse, and exposes the resulting trivial
joint kernel.  No generic rank/Gaussian-elimination theorem is required here.
-/

namespace Synthesis

#check syntheticBidiTwoVJointKernel_eq_bot
#check syntheticBidiTwoVJointlyInjective

end Synthesis
