import Integration.EisensteinJZeroPrimaryNormalizationExact

namespace Dashi.EisensteinJZeroPrimaryNormalizationValidation

open Dashi.EisensteinJZeroPrimaryNormalizationExact
open Dashi.EisensteinQuadraticAlgebraExact
open Dashi.EisensteinSixUnitsExact

example : IsJZeroPrimary (asQuadraticAlgebra (-3) (-2)) := by native_decide
example : ¬ IsJZeroPrimary (asQuadraticAlgebra 3 1) := by native_decide

#check splitPrime_primary_unit_exists
#check primary_unit_stabilizer_trivial
#check splitPrime_primary_unit_unique
#check splitPrime_primary_associate_existsUnique

end Dashi.EisensteinJZeroPrimaryNormalizationValidation
