import Integration.E6ProjectiveRootLineSRG

namespace DASHI.Integration.E6ProjectiveRootLineSRGRegression

open E6ProjectiveRootLineSRG

example : Fintype.card QTwoRootLine = 36 := qtwoRootLine_card
example : ∀ x : QTwoRootLine, (neighbors x).card = 15 := qtwoRootLine_degree15
example : ∀ x y : QTwoRootLine, x ≠ y → (commonNeighbors x y).card = 6 :=
  qtwoRootLine_common6

example : rootLineBoundary.vertexCount36Paid = true := rfl
example : rootLineBoundary.degree15Paid = true := rfl
example : rootLineBoundary.adjacentCommon6Paid = true := rfl
example : rootLineBoundary.nonAdjacentCommon6Paid = true := rfl

end DASHI.Integration.E6ProjectiveRootLineSRGRegression
