import Integration.EisensteinJZeroHeckeResidueUnitsExact

/-! RED-first regression for the six invertible residue classes modulo the
literal Hecke conductor `2*sqrt(-3)`. -/

namespace Integration.EisensteinJZeroHeckeResidueUnitsRegression

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinSixUnitOrbitExact
open Integration.EisensteinJZeroHeckeConductorExact
open Integration.EisensteinJZeroHeckeResidueUnitsExact

example (z : EisensteinQA) :
    heckeConductorElement ∣ z ↔
      (2 : Int) ∣ z.re ∧ (2 : Int) ∣ z.im ∧ (3 : Int) ∣ (z.re + z.im) :=
  heckeConductor_dvd_iff_coordinates z

example (z : EisensteinQA) (h : HeckeResidueAdmissible z) :
    HeckeUnitNormalizable z :=
  heckeUnitNormalizable_of_residueAdmissible z h

example (z : EisensteinQA) (h : HeckeResidueAdmissible z) :
    CongruentModHeckeConductor z
      (residueNormalizingUnit z h).1 :=
  residueNormalizingUnit_spec z h

end Integration.EisensteinJZeroHeckeResidueUnitsRegression
