import Integration.EisensteinLatticeCounting

namespace Dashi.EisensteinLatticeCountingRegression

open Dashi.EisensteinLatticeCounting

example : triangularNumber 10 = 55 := by native_decide
example : hexBallCount 3 = 37 := by native_decide
example : wedgeTriangleCount 3 = 10 := by native_decide
example : Nat.choose 4 2 = 6 := by native_decide

example : eisensteinDivisorShellCount 1 = 6 := by native_decide
example : eisensteinDivisorShellCount 2 = 0 := by native_decide
example : eisensteinDivisorShellCount 3 = 6 := by native_decide
example : eisensteinDivisorShellCount 4 = 6 := by native_decide
example : eisensteinDivisorShellCount 5 = 0 := by native_decide
example : eisensteinDivisorShellCount 6 = 0 := by native_decide
example : eisensteinDivisorShellCount 7 = 12 := by native_decide
example : eisensteinDivisorShellCount 8 = 0 := by native_decide
example : eisensteinDivisorShellCount 9 = 6 := by native_decide
example : eisensteinDivisorShellCount 10 = 0 := by native_decide

end Dashi.EisensteinLatticeCountingRegression
