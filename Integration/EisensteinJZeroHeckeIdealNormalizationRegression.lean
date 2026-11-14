import Integration.EisensteinJZeroHeckeIdealNormalizationExact

/-! RED-first regression for descent from conductor-coprime principal ideals
to uniquely normalized Eisenstein generators. -/

namespace Integration.EisensteinJZeroHeckeIdealNormalizationRegression

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroHeckeConductorExact
open Integration.EisensteinJZeroHeckeResidueUnitsExact
open Integration.EisensteinJZeroHeckeIdealNormalizationExact

example (z : EisensteinQA)
    (h : IsCoprime z heckeConductorElement) :
    HeckeResidueAdmissible z :=
  residueAdmissible_of_isCoprime_conductor z h

example (I : Ideal EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I) :
    HeckeUnitNormalizable (rawIdealGenerator I) :=
  rawIdealGenerator_normalizable I hI

example (I : Ideal EisensteinQA)
    (hI : IdealCoprimeToHeckeConductor I) :
    Ideal.span ({normalizedIdealGenerator I hI} : Set EisensteinQA) = I :=
  normalizedIdealGenerator_spans I hI

end Integration.EisensteinJZeroHeckeIdealNormalizationRegression
