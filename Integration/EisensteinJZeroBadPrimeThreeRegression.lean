import Integration.EisensteinJZeroBadPrimeThreeExact

/-! RED-first regression for the bad-prime-three reduction boundary. -/

namespace Integration.EisensteinJZeroBadPrimeThreeRegression

open Integration.EisensteinJZeroBadPrimeThreeExact

example : reducedCurveThreeEquation (2 : ZMod 3) 0 :=
  badReductionSingularPoint_on_curve

example : reducedCurveThreeDx (2 : ZMod 3) = 0 :=
  badReductionSingularPoint_dx

example : reducedCurveThreeDy (0 : ZMod 3) = 0 :=
  badReductionSingularPoint_dy

example : reducedCurveThreeAffinePointCount = 3 :=
  reducedCurveThreeAffinePointCount_exact

example : reducedCurveThreeProjectiveNaivePointCount = 4 :=
  reducedCurveThreeProjectiveNaivePointCount_exact

end Integration.EisensteinJZeroBadPrimeThreeRegression
