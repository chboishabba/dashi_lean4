import Integration.EisensteinSixUnitsExact

namespace Dashi.EisensteinSixUnitsValidation

open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinSixUnitsExact

/-- Unit classification is exact, not merely a cardinality assertion. -/
example (z : EisensteinQA) (hz : IsUnit z) :
    z = unitOne ∨ z = unitNegOne ∨
    z = unitOmega ∨ z = unitNegOmega ∨
    z = unitOmegaSquared ∨ z = unitNegOmegaSquared :=
  unit_classification z hz

example : Finset.card eisensteinUnits = 6 := by native_decide

example : ∀ z ∈ eisensteinUnits, IsUnit z :=
  all_listed_units_are_units

end Dashi.EisensteinSixUnitsValidation
