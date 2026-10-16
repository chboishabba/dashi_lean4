import Synthesis.ClosedDeSitterBounce

namespace Synthesis.ClosedDeSitterBounceRegression

example : scaleFactor 0 = 1 := scaleFactor_zero
example : scaleVelocity 0 = 0 := scaleVelocity_zero
example (t : ℝ) : scaleVelocity t ^ 2 + 1 = scaleFactor t ^ 2 := closedFriedmann
example (t : ℝ) : HasDerivAt scaleFactor (scaleVelocity t) t := scaleFactor_hasDerivAt
example (t : ℝ) : HasDerivAt scaleVelocity (scaleFactor t) t := scaleVelocity_hasDerivAt

end Synthesis.ClosedDeSitterBounceRegression
