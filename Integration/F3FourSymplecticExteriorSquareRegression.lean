import Integration.F3FourSymplecticExteriorSquare

namespace DASHI.Integration.F3FourSymplecticExteriorSquareRegression

open F3FourSymplecticExteriorSquare

example : Fintype.card RawPuncturedT4 = 80 := card_rawPuncturedT4
example : Fintype.card NullCone80 = 80 := card_nullCone80
example : lagrangianWedgeSet = nullConeFinset := lagrangianWedgeSet_eq_nullCone
example : lagrangianWedgeSet.card = 80 := card_lagrangianWedgeSet

example : exteriorSquareBoundary.rawPuncturedT4IdentifiedWithNullCone = false := rfl
example : exteriorSquareBoundary.derivedLagrangianNullConePaid = true := rfl
example : exteriorSquareBoundary.sameActionRecognitionStillRequired = true := rfl

end DASHI.Integration.F3FourSymplecticExteriorSquareRegression
