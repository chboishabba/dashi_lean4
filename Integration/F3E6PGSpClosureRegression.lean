import Integration.F3E6PGSpClosure

namespace DASHI.Integration.F3E6PGSpClosureRegression

open F3E6PGSpClosure

example : generatedClosure.card = 103680 := generatedClosure_card
example : closureStep generatedClosure = generatedClosure := generatedClosure_stable
example : exteriorKernel = ({1, -1} : Finset M4) := exteriorKernel_eq_plusMinusIdentity
example : exteriorKernel.card = 2 := exteriorKernel_card
example : generatedClosure.card / exteriorKernel.card = 51840 := projectiveQuotientOrder

example : closureBoundary.fourSpaceClosureOrder103680Paid = true := rfl
example : closureBoundary.exteriorKernelExactlyPlusMinusIPaid = true := rfl
example : closureBoundary.projectiveQuotientOrder51840Paid = true := rfl
example : closureBoundary.abstractPGSpQuotientWeylIsomorphismPaid = false := rfl

end DASHI.Integration.F3E6PGSpClosureRegression
