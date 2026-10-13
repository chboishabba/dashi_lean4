import Integration.EisensteinCharacterLocalFactorsExact

namespace Dashi.EisensteinCharacterLocalFactorsValidation

open Dashi.EisensteinCharacterLocalFactorsExact

example : localCharacterFactor 0 8 = 1 := by native_decide
example : localCharacterFactor 1 8 = 9 := by native_decide
example : localCharacterFactor (-1) 8 = 1 := by native_decide
example : localCharacterFactor (-1) 9 = 0 := by native_decide

end Dashi.EisensteinCharacterLocalFactorsValidation
