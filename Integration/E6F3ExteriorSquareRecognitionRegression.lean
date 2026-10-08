import Integration.E6F3ExteriorSquareRecognition

namespace Integration.E6F3ExteriorSquareRecognitionRegression

open Integration.E6F3ExteriorSquareRecognition

example : Fintype.card PrimitiveNull80 = 80 := primitiveNull80_card
example : Fintype.card StandardNull80 = 80 := standardNull80_card
example : Fintype.card PrimitiveProjectiveNull = 40 := primitiveProjectiveNull_card
example : Fintype.card StandardProjectiveNull = 40 := standardProjectiveNull_card

example : ∀ p, standardToPrimitive (primitiveToStandard p) = p := primitive_roundtrip_all
example : ∀ z, primitiveToStandard (standardToPrimitive z) = z := standard_roundtrip_all
example : ∀ p, standardQ (primitiveToStandard p) = -(pluckerQ p) := quadratic_intertwining_all

example : canonicalBoundary.rawPuncturedT4IdentifiedWithDerived80 = false := rfl
example : canonicalBoundary.literalPGSp4WeylGroupEqualityPaid = false := rfl

end Integration.E6F3ExteriorSquareRecognitionRegression
