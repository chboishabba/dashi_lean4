import Integration.EisensteinJZeroBadPrimeTwoExact

/-! RED-first regression for the bad-prime-two reduction boundary. -/

namespace Integration.EisensteinJZeroBadPrimeTwoRegression

open Integration.EisensteinJZeroBadPrimeTwoExact

example : reducedCurveTwoEquation (0 : ZMod 2) 1 :=
  badReductionSingularPoint_on_curve

example : reducedCurveTwoDx (0 : ZMod 2) = 0 :=
  badReductionSingularPoint_dx

example : reducedCurveTwoDy (1 : ZMod 2) = 0 :=
  badReductionSingularPoint_dy

example : reducedCurveTwoAffinePointCount = 2 :=
  reducedCurveTwoAffinePointCount_exact

example : reducedCurveTwoProjectiveNaivePointCount = 3 :=
  reducedCurveTwoProjectiveNaivePointCount_exact

end Integration.EisensteinJZeroBadPrimeTwoRegression
