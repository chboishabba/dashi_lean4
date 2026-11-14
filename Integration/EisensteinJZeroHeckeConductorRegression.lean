import Integration.EisensteinJZeroHeckeConductorExact

/-!
RED-first regression for the same-carrier Hecke-conductor layer.

The external CM literature identifies the normalization modulus for
`y^2=x^3+1` as `(2*sqrt(-3))`.  The production owner must realize that modulus
inside the literal repo `EisensteinQA` carrier and expose the exact
six-unit-congruence seam needed for globalization.
-/

namespace Integration.EisensteinJZeroHeckeConductorRegression

open Dashi.EisensteinQuadraticAlgebraExact
open Integration.EisensteinJZeroHeckeConductorExact

example : sqrtMinusThreeEisenstein ^ 2 = (-3 : EisensteinQA) :=
  sqrtMinusThreeEisenstein_sq

example : heckeConductorElement = asQuadraticAlgebra 2 4 :=
  heckeConductorElement_coordinates

example : QuadraticAlgebra.norm heckeConductorElement = 12 :=
  heckeConductorElement_norm

example : 12 * 3 = 36 := conductorNorm_times_fieldDiscriminant

example (z : EisensteinQA) : Prop := HeckeUnitNormalizable z

example (z : EisensteinQA) (h : HeckeUnitNormalizable z) :
    Dashi.EisensteinSixUnitOrbitExact.EisensteinUnitCode :=
  normalizedHeckeUnit z h

end Integration.EisensteinJZeroHeckeConductorRegression
