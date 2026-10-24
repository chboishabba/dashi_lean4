import Integration.EisensteinJZeroFiniteEulerProductExact

namespace Integration.EisensteinJZeroFiniteEulerProductValidation

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroFiniteEulerProductExact

example (p : RationalPrime) (T : EisensteinQA) :
    ellipticPrimeEulerPolynomial p T = heckePrimeEulerPolynomial p T :=
  elliptic_hecke_primePolynomial_agreement p T

example (S : Finset RationalPrime) (T : EisensteinQA) :
    ellipticFiniteEulerDenominator S T = heckeFiniteEulerDenominator S T :=
  finiteEulerDenominator_agreement S T

end Integration.EisensteinJZeroFiniteEulerProductValidation
