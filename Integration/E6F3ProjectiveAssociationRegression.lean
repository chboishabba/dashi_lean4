import Integration.E6F3ProjectiveAssociation

namespace Integration.E6F3ProjectiveAssociationRegression

open Integration.E6F3ProjectiveAssociation

example : Fintype.card NullLine = 40 := nullLine_card
example : Fintype.card Q1Line = 45 := q1Line_card
example : Fintype.card Q2Line = 36 := q2Line_card

example : ∀ x : NullLine, nullDegree x = 12 := null_degree_12
example : ∀ x y : NullLine, nullAdjacent x y = true → nullCommon x y = 2 :=
  null_adjacent_common_2
example : ∀ x y : NullLine, x ≠ y → nullAdjacent x y = false → nullCommon x y = 4 :=
  null_nonadjacent_common_4

example : ∀ x : Q1Line, q1Degree x = 12 := q1_degree_12
example : ∀ x y : Q1Line, q1Adjacent x y = true → q1Common x y = 3 :=
  q1_adjacent_common_3
example : ∀ x y : Q1Line, x ≠ y → q1Adjacent x y = false → q1Common x y = 3 :=
  q1_nonadjacent_common_3

example : ∀ x : Q2Line, q2Degree x = 15 := q2_degree_15
example : ∀ x y : Q2Line, q2Adjacent x y = true → q2Common x y = 6 :=
  q2_adjacent_common_6
example : ∀ x y : Q2Line, x ≠ y → q2Adjacent x y = false → q2Common x y = 6 :=
  q2_nonadjacent_common_6

example : canonicalBoundary.q2SRG361566Paid = true := rfl
example : canonicalBoundary.q1SRG451233Paid = true := rfl
example : canonicalBoundary.nullSRG401224Paid = true := rfl

end Integration.E6F3ProjectiveAssociationRegression
