import Integration.EisensteinJZeroHeckeLocalAgreementExact

namespace Integration.EisensteinJZeroHeckeLocalAgreementValidation

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroHeckeLocalAgreementExact

example (p : Nat) [Fact p.Prime] (hp3 : 3 < p) (hmod : p % 3 = 2) :
    finiteIdealHeckeCharacter (inertPrimeIdealCode p hp3 hmod) =
      inertHeckeFactor p :=
  finiteIdealHeckeCharacter_inertPrime p hp3 hmod

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    finiteIdealHeckeCharacter (splitPrimeIdealCode p hmod) =
      Integration.EisensteinJZeroSplitEulerFactorExact.jacobiFrobeniusPrime p hmod :=
  finiteIdealHeckeCharacter_splitPrime p hmod

example (p : Nat) [Fact p.Prime] (hmod : p % 3 = 1) :
    finiteIdealHeckeCharacter (splitConjugatePrimeIdealCode p hmod) =
      star (Integration.EisensteinJZeroSplitEulerFactorExact.jacobiFrobeniusPrime p hmod) :=
  finiteIdealHeckeCharacter_splitConjugatePrime p hmod

example (p : Nat) [Fact p.Prime] (hp3 : 3 < p) (T : EisensteinQA) :
    heckeRationalPrimeEulerPolynomial p hp3 T =
      ellipticGoodPrimeEulerPolynomialEisenstein p hp3 T :=
  hecke_elliptic_goodPrime_local_agreement p hp3 T

end Integration.EisensteinJZeroHeckeLocalAgreementValidation
