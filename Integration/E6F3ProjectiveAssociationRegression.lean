import Integration.E6F3ProjectiveAssociation

namespace Integration.E6F3ProjectiveAssociationRegression

open Integration.E6F3ProjectiveAssociation

example : Fintype.card NullLine = 40 := nullLine_card
example : Fintype.card Q1Line = 45 := q1Line_card
example : Fintype.card Q2Line = 36 := q2Line_card
example : ∀ x : NullLine, nullDegree x = 12 := null_degree_12
example : ∀ x : Q1Line, q1Degree x = 12 := q1_degree_12
example : ∀ x : Q2Line, q2Degree x = 15 := q2_degree_15
example : canonicalBoundary.q2SRG361566Paid = true := rfl
example : canonicalBoundary.q1SRG451233Paid = true := rfl
example : canonicalBoundary.nullSRG401224Paid = true := rfl

end Integration.E6F3ProjectiveAssociationRegression
