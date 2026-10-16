import Integration.E6RootLineSameObject
import Integration.E6F3ProjectiveStrataSRG
import Integration.E6F3DepthQuadraticInteraction
import Integration.F3E6PGSpClosure
import Integration.F3E6ProjectiveIncidenceDuality

namespace DASHI.Integration.E6F3FiniteGeometryMaxCutRegression

open DASHI.Integration.E6RootLineSameObject
open DASHI.Integration.E6F3ProjectiveStrataSRG
open DASHI.Integration.E6F3DepthQuadraticInteraction
open DASHI.Integration.F3E6PGSpClosure
open DASHI.Integration.F3E6ProjectiveIncidenceDuality

example : Fintype.card E6RootLine = 36 := e6RootLine_card
example : sameObjectBoundary.literalRootLineQTwoEquivalencePaid = true := rfl
example : sameObjectBoundary.literalE6RootLineSRG361566Paid = true := rfl

example : Fintype.card QZeroLine = 40 := qzeroLine_card
example : Fintype.card QOneLine = 45 := qoneLine_card
example : Fintype.card QTwoLine = 36 := qtwoLine_card
example :
    Fintype.card QZeroLine + Fintype.card QOneLine + Fintype.card QTwoLine = 121 :=
  projective_partition_121
example : strataBoundary.qoneSRG451233Paid = true := rfl

example : depth1Profile 0 = ⟨1,32,24,24⟩ := depth1_zero_profile
example : depth1Profile 1 = ⟨0,24,33,24⟩ := depth1_one_profile
example : depth2Profile 0 0 = ⟨1,8,6,12⟩ := depth2_zero_zero_profile
example : depth1Profile 0 ≠ depth1Profile 1 := depth_quadratic_not_cartesian_product

example : generatedClosure.card = 103680 := generatedClosure_card
example : exteriorKernel.card = 2 := exteriorKernel_card
example : generatedClosure.card / exteriorKernel.card = 51840 := projectiveQuotientOrder
example : incidenceBoundary.projectiveSRG401224Paid = true := rfl

end DASHI.Integration.E6F3FiniteGeometryMaxCutRegression
