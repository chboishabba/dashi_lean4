import Integration.EisensteinJZeroQuadraticCharacterTraceExact

namespace Dashi.EisensteinJZeroQuadraticCharacterTraceValidation

open Dashi.EisensteinJZeroQuadraticCharacterTraceExact

#check squareFiberCard_eq_one_add_quadraticChar
#check affinePointCount_eq_card_add_characterSum
#check frobeniusTrace_eq_neg_characterSum

example : jZeroQuadraticCharacterSum 5 = 0 := by native_decide
example : jZeroQuadraticCharacterSum 7 = 4 := by native_decide

end Dashi.EisensteinJZeroQuadraticCharacterTraceValidation
