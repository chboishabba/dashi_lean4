import Integration.ExceptionalE6Mod3FiniteGeometry

namespace Integration.ExceptionalE6Mod3FiniteGeometryRegression

open Integration.ExceptionalE6Mod3FiniteGeometry

example : Fintype.card V5 = 243 := total_state_count
example : Fintype.card NullNonzero = 80 := null_nonzero_count
example : Fintype.card ClassOne = 90 := class_one_count
example : Fintype.card ClassTwo = 72 := class_two_count
example : Fintype.card NullLines = 40 := null_line_count
example : Fintype.card RootCandidateLines = 36 := root_candidate_line_count
example : Fintype.card OtherNonsingularLines = 45 := other_nonsingular_line_count
example : canonicalBoundary.e6RootRecognitionInhabitedHere = false := rfl
example : canonicalBoundary.faithfulWeylRecognitionInhabitedHere = false := rfl
example : canonicalBoundary.e6E8DualIncidenceRecognitionInhabitedHere = false := rfl
example : canonicalBoundary.t4LinearIdentificationClaimed = false := rfl
example : canonicalBoundary.depthNormProductClaimed = false := rfl

end Integration.ExceptionalE6Mod3FiniteGeometryRegression
