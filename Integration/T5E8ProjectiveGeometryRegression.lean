import Integration.T5E8ProjectiveGeometry

namespace Integration.T5E8ProjectiveGeometryRegression

open Integration.T5E8ProjectiveGeometry

example : Fintype.card ProjectiveRelativeT5 = 120 := projective_relative_t5_count
example : noCirculantCandidateHasE8Valency := no_circulant_candidate_has_e8_valency
example : canonicalBoundary.projectiveRelativeCount120Paid = true := rfl
example : canonicalBoundary.symmetricCirculantFamily27Typed = true := rfl
example : canonicalBoundary.e8Valency56CandidateFound = false := rfl
example : canonicalBoundary.fullE8GeometryRecognized = false := rfl

end Integration.T5E8ProjectiveGeometryRegression
