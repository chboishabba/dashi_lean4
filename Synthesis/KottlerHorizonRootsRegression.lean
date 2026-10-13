import Synthesis.KottlerHorizonRoots

namespace Synthesis.KottlerHorizonRootsRegression

example : horizonPolynomial (1 / 2 : ℝ) = 1 / 8 := innerLeft_value
example : horizonPolynomial (13 / 25 : ℝ) = -(2803 / 15625 : ℝ) := innerRight_value
example : ∃ r ∈ Set.Icc (1 / 2 : ℝ) (13 / 25 : ℝ), horizonPolynomial r = 0 := innerHorizon_exists
example : ∃ r ∈ Set.Icc (37 / 10 : ℝ) (15 / 4 : ℝ), horizonPolynomial r = 0 := outerHorizon_exists

end Synthesis.KottlerHorizonRootsRegression
