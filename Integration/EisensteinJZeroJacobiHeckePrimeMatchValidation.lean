import Integration.EisensteinJZeroJacobiHeckePrimeMatchExact

namespace Integration.EisensteinJZeroJacobiHeckePrimeMatchValidation

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroHeckeConductorExact
open Integration.EisensteinJZeroIntegralHeckeCharacterExact
open Integration.EisensteinJZeroJacobiHeckePrimeMatchExact

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    CongruentModHeckeConductor
      (Integration.EisensteinJZeroSplitEulerFactorExact.jacobiFrobeniusPrime p hmod) 1 :=
  jacobiFrobeniusPrime_congruent_one p hmod

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    IdealCoprimeToHeckeConductor (jacobiFrobeniusIdeal p hmod) :=
  jacobiFrobeniusIdeal_coprime p hmod

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    integralHeckeCharacter (jacobiFrobeniusIdealCode p hmod) =
      Integration.EisensteinJZeroSplitEulerFactorExact.jacobiFrobeniusPrime p hmod :=
  integralHeckeCharacter_jacobiFrobeniusIdeal p hmod

end Integration.EisensteinJZeroJacobiHeckePrimeMatchValidation
