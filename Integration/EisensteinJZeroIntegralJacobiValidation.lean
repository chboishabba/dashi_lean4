import Integration.EisensteinJZeroIntegralJacobiExact

namespace Integration.EisensteinJZeroIntegralJacobiValidation

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroIntegralJacobiExact

example : IsPrimitiveRoot (QuadraticAlgebra.omega : EisensteinQA) 3 :=
  eisensteinOmega_isPrimitiveRoot_three

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    orderOf (eisensteinCubicCharacter p hmod) = 3 :=
  eisensteinCubicCharacter_order p hmod

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    QuadraticAlgebra.norm (eisensteinMixedJacobi p hmod) = p :=
  eisensteinMixedJacobi_norm p hmod

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    QuadraticAlgebra.trace (eisensteinMixedJacobi p hmod) =
      -Integration.EisensteinJZeroFiniteFieldTraceExact.jZeroFrobeniusTraceInt (ZMod p) :=
  eisensteinMixedJacobi_trace p hmod

end Integration.EisensteinJZeroIntegralJacobiValidation
