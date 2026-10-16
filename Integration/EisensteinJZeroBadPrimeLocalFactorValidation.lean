import Integration.EisensteinJZeroBadPrimeLocalFactorExact

namespace Integration.EisensteinJZeroBadPrimeLocalFactorValidation

open Integration.EisensteinJZeroBadPrimeLocalFactorExact

example : badPrimeTwoAffineSingularCount = 1 :=
  badPrimeTwoAffineSingularCount_exact

example : badPrimeThreeAffineSingularCount = 1 :=
  badPrimeThreeAffineSingularCount_exact

example : badPrimeTwoNonsingularProjectiveCount = 2 :=
  badPrimeTwoNonsingularProjectiveCount_exact

example : badPrimeThreeNonsingularProjectiveCount = 3 :=
  badPrimeThreeNonsingularProjectiveCount_exact

example : badPrimeTwoLocalTrace = 0 := badPrimeTwoLocalTrace_zero
example : badPrimeThreeLocalTrace = 0 := badPrimeThreeLocalTrace_zero

example {R : Type*} [CommRing R] (T : R) :
    badPrimeTwoLocalEulerFactor T = 1 := badPrimeTwoLocalEulerFactor_one T

example {R : Type*} [CommRing R] (T : R) :
    badPrimeThreeLocalEulerFactor T = 1 := badPrimeThreeLocalEulerFactor_one T

end Integration.EisensteinJZeroBadPrimeLocalFactorValidation
