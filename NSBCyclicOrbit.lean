import NSBControl.CyclicHelicalVectorTransform

namespace NSBCyclicOrbit

open NSBControl.CyclicHelicalVectorTransform

example (a b : ℝ) : (-b) - a = -(a + b) := by
  exact plusMinusCoefficient a b

example (a b : ℝ) : b - (-a) = a + b := by
  exact minusPlusCoefficient a b

example (a b : ℝ) : (-b) - (-a) = a - b := by
  exact minusMinusCoefficient a b

end NSBCyclicOrbit
