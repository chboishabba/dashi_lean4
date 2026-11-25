import Integration.E6Minuscule27SchlafliRecognition

namespace Integration.E6Minuscule27SchlafliRecognitionRegression

open Integration.E6Minuscule27SchlafliRecognition

example : Fintype.card Omega5Weight = 27 := omega5_weight_card
example : ∀ x : Omega5Weight, omega5Degree x = 16 := omega5_degree_16
example : canonicalBoundary.omega5SchlafliParametersPaid = true := rfl
example : canonicalBoundary.literalSixFibreRelationEqualityPaid = true := rfl
example : canonicalBoundary.minusculeWeightGeometryRecognized = true := rfl
example : canonicalBoundary.albertJordanProductPaid = false := rfl

end Integration.E6Minuscule27SchlafliRecognitionRegression
