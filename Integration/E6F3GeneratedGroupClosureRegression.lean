import Integration.E6F3GeneratedGroupClosure

namespace Integration.E6F3GeneratedGroupClosureRegression

open Integration.E6F3GeneratedGroupClosure

example : generatedMatrixSet.card = 51840 := generated_matrix_set_card
example : generatedMatrixSet = matrixOrbitN 36 := rfl
example : matrixOrbitN 37 = generatedMatrixSet := generated_matrix_set_stable
example : q2SeedStabilizer.card = 720 := q2_seed_stabilizer_card
example : 51840 = 72 * 720 := by norm_num
example : canonicalBoundary.generatedImageOrder51840Paid = true := rfl
example : canonicalBoundary.q2RootStabilizerOrder720Paid = true := rfl
example : canonicalBoundary.stabilizerIdentifiedAsS6ByOrderAlone = false := rfl
example : canonicalBoundary.fullPGSp4EqualsWE6PaidHere = false := rfl

end Integration.E6F3GeneratedGroupClosureRegression
