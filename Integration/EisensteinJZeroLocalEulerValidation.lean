import Integration.EisensteinJZeroLocalEulerExact

namespace Dashi.EisensteinJZeroLocalEulerValidation

open Dashi.EisensteinJZeroLocalEulerExact

example : affinePointCount5 = 5 := by native_decide
example : projectivePointCount5 = 6 := by native_decide
example : frobeniusTrace5 = 0 := by native_decide
example : localEulerAt5 = (1, 0, 5) := by native_decide
example : 5 % 3 = 2 := by native_decide

#check inertFiveTraceZero
#check inertFiveLocalFactor

end Dashi.EisensteinJZeroLocalEulerValidation
