import Integration.EisensteinLatticeCounting
import Integration.EisensteinLatticeCountingMaxCut

namespace Dashi.EisensteinLatticeCountingRegression

open Dashi.EisensteinLatticeCounting
open Dashi.EisensteinLatticeCountingMaxCut

example : triangularNumber 10 = 55 := by native_decide
example : hexBallCount 3 = 37 := by native_decide
example : wedgeTriangleCount 3 = 10 := by native_decide
example : Nat.choose 4 2 = 6 := by native_decide
example : pascalRowSum 8 = 256 := by native_decide
example : hexBallCount 10 = 331 := by native_decide

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

example : eisensteinNorm 2 1 = 3 := by native_decide
example : rotate (2,1) = (1,2) := by native_decide
example : rotate (rotate (rotate (rotate (rotate (rotate (2,1)))))) = (2,1) := by native_decide

end Dashi.EisensteinLatticeCountingRegression
