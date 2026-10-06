import Integration.E6F3ExteriorSquare

namespace Integration.E6F3ExteriorSquareRegression

open Integration.E6F3ExteriorSquare

example : Fintype.card RawT4Punctured = 80 := rawT4Punctured_card
example : Fintype.card PrimitiveNull = 80 := primitiveNull_card
example : Fintype.card StandardNull = 80 := standardNull_card
example : Fintype.card StandardQ1 = 90 := standardQ1_card
example : Fintype.card StandardQ2 = 72 := standardQ2_card
example : canonicalBoundary.rawT4KeptDistinctFromDerivedLag80 = true := rfl
example : canonicalBoundary.cardinalityAlonePromotesRecognition = false := rfl
example : canonicalBoundary.primitiveStandardIsometryPaid = true := rfl
example : canonicalBoundary.pluckerNullFromIsotropyPaid = true := rfl

end Integration.E6F3ExteriorSquareRegression
