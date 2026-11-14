import Integration.EisensteinJZeroHeckeIdealCharacterExact

/-! RED-first regression for multiplicativity of conductor-normalized ideal
generators and the resulting finite ideal character. -/

namespace Integration.EisensteinJZeroHeckeIdealCharacterRegression

open Integration.EisensteinJZeroHeckeConductorExact
open Integration.EisensteinJZeroHeckeIdealNormalizationExact
open Integration.EisensteinJZeroHeckeIdealCharacterExact

example (I J : Ideal Dashi.EisensteinQuadraticAlgebraExact.EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I)
    (hJ : IdealCoprimeToHeckeConductor J) :
    IdealCoprimeToHeckeConductor (I * J) :=
  idealMul_coprime_conductor I J hI hJ

example (I : Ideal Dashi.EisensteinQuadraticAlgebraExact.EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I) :
    CongruentModHeckeConductor (normalizedIdealGenerator I hI) 1 :=
  normalizedIdealGenerator_congruent_one I hI

example (I J : Ideal Dashi.EisensteinQuadraticAlgebraExact.EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I)
    (hJ : IdealCoprimeToHeckeConductor J) :
    normalizedIdealGenerator (I * J) (idealMul_coprime_conductor I J hI hJ) =
      normalizedIdealGenerator I hI * normalizedIdealGenerator J hJ :=
  normalizedIdealGenerator_mul I J hI hJ

example :
    HeckeCoprimeIdealSubmonoid →* Dashi.EisensteinQuadraticAlgebraExact.EisensteinQA :=
  finiteIdealHeckeCharacter

end Integration.EisensteinJZeroHeckeIdealCharacterRegression
