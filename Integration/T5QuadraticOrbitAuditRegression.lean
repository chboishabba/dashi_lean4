import Integration.T5QuadraticOrbitAudit

namespace Integration.T5QuadraticOrbitAuditRegression

open Integration.T5QuadraticOrbitAudit

example : Fintype.card QZeroShell = 81 := qzero_shell_card
example : Fintype.card QOneShell = 90 := qone_shell_card
example : Fintype.card QTwoShell = 72 := qtwo_shell_card
example : Fintype.card QZeroNonzeroShell = 80 := qzero_nonzero_shell_card

example : qT5 negativeDiagonal = 2 := q_negative_diagonal
example : qT5 zeroDiagonal = 0 := q_zero_diagonal
example : qT5 positiveDiagonal = 2 := q_positive_diagonal

example : Fintype.card RelativeQZeroShell = 80 := relative_qzero_shell_card
example : Fintype.card RelativeQOneShell = 90 := relative_qone_shell_card
example : Fintype.card RelativeQTwoShell = 70 := relative_qtwo_shell_card

example : canonicalBoundary.fullT5OrbitPartitionOnePlusEightyPlusNinetyPlusSeventyTwo = true := rfl
example : canonicalBoundary.relative240IsNotTheQTwoShell = true := rfl
example : canonicalBoundary.cardinality240CreatesE8Recognition = false := rfl

end Integration.T5QuadraticOrbitAuditRegression
