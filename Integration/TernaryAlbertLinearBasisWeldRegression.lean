import Integration.TernaryAlbertLinearBasisWeld

namespace Integration.TernaryAlbertLinearBasisWeldRegression

open Integration.TernaryAlbertLinearBasisWeld

example : Fintype.card NonOrigin26 = 26 := nonorigin_card_26
example : originSplit ternaryOrigin = Sum.inl () := originSplit_origin
example : canonicalBoundary.actualTernaryOriginTyped = true := rfl
example : canonicalBoundary.nonOriginCount26Paid = true := rfl
example : canonicalBoundary.originPlus26SplitPaid = true := rfl
example : canonicalBoundary.fin26TracelessBasisFromDimensionPaid = true := rfl
example : canonicalBoundary.linearTernaryBasisTransportInhabited = true := rfl
example : canonicalBoundary.f4EquivariancePaidHere = false := rfl
example : canonicalBoundary.jordanCubicCompatibilityPaidHere = false := rfl

end Integration.TernaryAlbertLinearBasisWeldRegression
