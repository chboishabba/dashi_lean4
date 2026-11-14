import Integration.EisensteinJZeroHeckeMultiplicativityExact

namespace Integration.EisensteinJZeroHeckeMultiplicativityValidation

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroHeckeConductorExact
open Integration.EisensteinJZeroHeckeIdealNormalizationExact
open Integration.EisensteinJZeroHeckeMultiplicativityExact

example {z w z' w' : EisensteinQA}
    (hz : CongruentModHeckeConductor z z')
    (hw : CongruentModHeckeConductor w w') :
    CongruentModHeckeConductor (z * w) (z' * w') :=
  congruentModHeckeConductor_mul hz hw

example (z : EisensteinQA) (hz : HeckeUnitNormalizable z) :
    CongruentModHeckeConductor (heckeNormalizedElement z hz) 1 :=
  heckeNormalizedElement_congruent_one z hz

example (z w : EisensteinQA)
    (hz : HeckeUnitNormalizable z) (hw : HeckeUnitNormalizable w) :
    HeckeUnitNormalizable (z * w) :=
  heckeUnitNormalizable_mul z w hz hw

example (z w : EisensteinQA)
    (hz : HeckeUnitNormalizable z) (hw : HeckeUnitNormalizable w) :
    heckeNormalizedElement (z * w) (heckeUnitNormalizable_mul z w hz hw) =
      heckeNormalizedElement z hz * heckeNormalizedElement w hw :=
  heckeNormalizedElement_mul z w hz hw

example (I J : Ideal EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I)
    (hJ : IdealCoprimeToHeckeConductor J) :
    normalizedIdealGenerator (I * J) (idealMul_coprime_conductor I J hI hJ) =
      normalizedIdealGenerator I hI * normalizedIdealGenerator J hJ :=
  normalizedIdealGenerator_mul I J hI hJ

end Integration.EisensteinJZeroHeckeMultiplicativityValidation
