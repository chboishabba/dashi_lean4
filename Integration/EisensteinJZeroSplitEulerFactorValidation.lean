import Integration.EisensteinJZeroSplitEulerFactorExact

namespace Integration.EisensteinJZeroSplitEulerFactorValidation

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroSplitEulerFactorExact

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    QuadraticAlgebra.norm (jacobiFrobeniusPrime p hmod) = p :=
  jacobiFrobeniusPrime_norm p hmod

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    QuadraticAlgebra.trace (jacobiFrobeniusPrime p hmod) =
      Integration.EisensteinJZeroFiniteFieldTraceExact.jZeroFrobeniusTraceInt (ZMod p) :=
  jacobiFrobeniusPrime_trace p hmod

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) (T : EisensteinQA) :
    (1 - jacobiFrobeniusPrime p hmod * T) *
        (1 - star (jacobiFrobeniusPrime p hmod) * T) =
      1 - algebraMap Int EisensteinQA
          (Integration.EisensteinJZeroFiniteFieldTraceExact.jZeroFrobeniusTraceInt (ZMod p)) * T +
        algebraMap Int EisensteinQA p * T ^ 2 :=
  splitPrimeEulerFactor_factorization p hmod T

end Integration.EisensteinJZeroSplitEulerFactorValidation
