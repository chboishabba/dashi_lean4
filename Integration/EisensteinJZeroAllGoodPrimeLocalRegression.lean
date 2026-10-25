import Integration.EisensteinJZeroAllGoodPrimeLocalExact

/-! RED-first regression for the complete good-prime local j=0 classification. -/

namespace Integration.EisensteinJZeroAllGoodPrimeLocalRegression

open Integration.EisensteinJZeroAllGoodPrimeLocalExact

example (p : Nat) [Fact p.Prime] (hp3 : 3 < p) :
    GoodPrimeLocalData p := goodPrimeLocalData p hp3

example (p : Nat) [Fact p.Prime] (hp3 : 3 < p) :
    goodPrimeLocalEulerPolynomial p hp3 =
      fun T => 1 -
        Integration.EisensteinJZeroFiniteFieldTraceExact.jZeroFrobeniusTraceInt (ZMod p) * T
        + p * T ^ 2 :=
  goodPrimeLocalEulerPolynomial_eq_curve p hp3

end Integration.EisensteinJZeroAllGoodPrimeLocalRegression
