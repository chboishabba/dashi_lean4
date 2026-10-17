import Integration.Ternary27HyperformSchlafliRecognition

namespace Integration.Ternary27HyperformSchlafliRecognitionRegression

open Integration.Ternary27HyperformSchlafliRecognition

example : Fintype.card Ternary27Point = 27 := ternary27_card
example : Fintype.card SchlafliLabel = 27 := label27_card
example : ∀ x, pointDegree pointSchlafli x = 16 := typed_hypervoxel_schlafli_degree_16
example : ∀ x, pointDegree pointOrthogonal x = 10 := typed_hypervoxel_orthogonal_degree_10
example : Function.Bijective pointToOmega5 := point_to_omega5_bijective
example : canonicalBoundary.absoluteSixFaceChartTyped = true := rfl
example : canonicalBoundary.ternary27ToSixFifteenSixBijectionPaid = true := rfl
example : canonicalBoundary.schlafliSRG2716108Paid = true := rfl
example : canonicalBoundary.omega5MinusculeRelationSameObjectPaid = true := rfl
example : canonicalBoundary.translationInvariantCayleyRelation = false := rfl
example : canonicalBoundary.independentPreexistingE6ActionOnRawTernaryPaid = false := rfl
example : canonicalBoundary.albertJordanProductPaid = false := rfl

end Integration.Ternary27HyperformSchlafliRecognitionRegression
