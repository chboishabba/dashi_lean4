import Integration.E8LiteralMixed27Schlafli

namespace Integration.E8LiteralMixed27SchlafliRegression

open Integration.E8LiteralMixed27Schlafli

example : ∀ x : Plus0, schlafliDegree x = 16 := plus0_degree_16
example : ∀ x y : Plus0, schlafliAdjacent x y = true → schlafliCommon x y = 10 :=
  plus0_adjacent_common_10
example : ∀ x y : Plus0, x ≠ y → schlafliAdjacent x y = false → schlafliCommon x y = 8 :=
  plus0_nonadjacent_common_8
example : ∀ x : Plus0, orthogonalDegree x = 10 := plus0_orthogonal_degree_10
example : ∀ x y : Plus0, orthogonalAdjacent x y = true → orthogonalCommon x y = 1 :=
  plus0_orthogonal_adjacent_common_1
example : ∀ x y : Plus0, x ≠ y → orthogonalAdjacent x y = false → orthogonalCommon x y = 5 :=
  plus0_orthogonal_nonadjacent_common_5
example : canonicalBoundary.schlafliSRG2716108Paid = true := rfl
example : canonicalBoundary.orthogonalComplementSRG271015Paid = true := rfl
example : canonicalBoundary.albertRecognitionFromCardinalityAlone = false := rfl

end Integration.E8LiteralMixed27SchlafliRegression
