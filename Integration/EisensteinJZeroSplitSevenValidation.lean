import Integration.EisensteinJZeroSplitSevenExact

namespace Dashi.EisensteinJZeroSplitSevenValidation

open Dashi.EisensteinJZeroSplitSevenExact

example : Fintype.card (JZeroAffinePoint 7) = 11 := by native_decide
example : splitSevenProjectiveCount = 12 := by native_decide
example : splitSevenFrobeniusTrace = -4 := by native_decide
example : splitSevenLocalEulerPolynomial = (1, 4, 7) := by native_decide

example : eisensteinNorm (-3) (-2) = 7 := by native_decide
example : eisensteinFieldTrace (-3) (-2) = -4 := by native_decide
example : eisensteinNorm 3 1 = 7 := by native_decide
example : eisensteinFieldTrace 3 1 = 5 := by native_decide

#check normalizedSevenMatchesFrobeniusTrace
#check normSevenDoesNotDetermineTrace

end Dashi.EisensteinJZeroSplitSevenValidation
