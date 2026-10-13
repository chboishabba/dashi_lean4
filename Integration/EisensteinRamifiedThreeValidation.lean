import Integration.EisensteinRamifiedThreeExact

namespace Dashi.EisensteinRamifiedThreeValidation

open Dashi.EisensteinRamifiedThreeExact

example : QuadraticAlgebra.norm ramifiedPrime = 3 := by native_decide
example : ramifiedPrime * ramifiedPrime = minusThreeOmega := by native_decide

end Dashi.EisensteinRamifiedThreeValidation
