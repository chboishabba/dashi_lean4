import Integration.EisensteinJZeroAllPrimeLocalExact

namespace Integration.EisensteinJZeroAllPrimeLocalValidation

open Integration.EisensteinJZeroAllPrimeLocalExact

example : allPrimeLocalEulerPolynomial 2 = fun _ : Int => 1 :=
  allPrimeLocalEulerPolynomial_two

example : allPrimeLocalEulerPolynomial 3 = fun _ : Int => 1 :=
  allPrimeLocalEulerPolynomial_three

example (p : Nat) [Fact p.Prime] (hp3 : 3 < p) :
    allPrimeLocalEulerPolynomial p =
      Integration.EisensteinJZeroAllGoodPrimeLocalExact.goodPrimeLocalEulerPolynomial p hp3 :=
  allPrimeLocalEulerPolynomial_good p hp3

example (p : Nat) [Fact p.Prime] (hp3 : 3 < p) (hmod : p % 3 = 2) :
    allPrimeLocalEulerPolynomial p = fun T : Int => 1 + p * T ^ 2 :=
  allPrimeLocalEulerPolynomial_inert p hp3 hmod

end Integration.EisensteinJZeroAllPrimeLocalValidation
