import Integration.E8ExceptionalBranchingBridge

namespace Integration.E8ExceptionalBranchingRegression

open Integration.E8ExceptionalBranchingBridge

example : 240 = 72 + 6 + 3 * 27 + 3 * 27 := by norm_num
example : 248 = 78 + 8 + 3 * 27 + 3 * 27 := by norm_num
example : 240 = 126 + 2 + 56 + 56 := by norm_num
example : 248 = 133 + 3 + 56 + 56 := by norm_num
example : canonicalBoundary.rootFibre27IsAlbertRepresentationHere = false := rfl
example : canonicalBoundary.rootFibre56IsFreudenthalRepresentationHere = false := rfl

end Integration.E8ExceptionalBranchingRegression
