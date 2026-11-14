import Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact

/-!
RED-first regression for the literal cyclotomic-Jacobi -> `EisensteinQA`
carrier weld and split-prime Frobenius formula.
-/

namespace Integration.EisensteinJZeroSplitPrimeEisensteinCarrierRegression

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroSplitPrimeEisensteinCarrierExact

example : omegaComplex ^ 2 = -1 - omegaComplex := omegaComplex_square

example : Function.Injective eisensteinComplexEmbedding :=
  eisensteinComplexEmbedding_injective

example (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    QuadraticAlgebra.norm (splitJacobiEisensteinElement p hp2 hp3) = p :=
  splitJacobiEisensteinElement_norm p hp2 hp3

example (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    Integration.EisensteinJZeroFiniteFieldTraceExact.jZeroFrobeniusTraceInt (ZMod p)
      = -(2 * (splitJacobiEisensteinElement p hp2 hp3).re
          - (splitJacobiEisensteinElement p hp2 hp3).im) :=
  splitPrime_jZero_trace_formula p hp2 hp3

example (p : Nat) [Fact p.Prime] (hp2 : 2 < p) (hp3 : p % 3 = 1) :
    splitPrimeLocalEulerPolynomial p hp2 hp3 =
      fun T => 1 +
        (2 * (splitJacobiEisensteinElement p hp2 hp3).re
          - (splitJacobiEisensteinElement p hp2 hp3).im) * T + p * T ^ 2 :=
  splitPrimeLocalEulerPolynomial_formula p hp2 hp3

end Integration.EisensteinJZeroSplitPrimeEisensteinCarrierRegression
