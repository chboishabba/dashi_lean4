import Integration.TetracodeE8ExplicitMap

namespace Integration.TetracodeE8ExplicitMapRegression

open Integration.TetracodeE8ExplicitMap

example : canonicalExecution.tetracodeWordCount = 9 := rfl
example : canonicalExecution.minimalShellCount = 240 := rfl
example : canonicalExecution.zeroResidueMinimalCount = 24 := rfl
example : canonicalExecution.nonzeroResidueMinimalCount = 216 := rfl
example : canonicalExecution.standardIntegerRootCount = 112 := rfl
example : canonicalExecution.standardHalfRootCount = 128 := rfl
example : canonicalExecution.explicitMatrixImageEqualsStandardE8 = true := rfl
example : canonicalBoundary.relativeT5RecognizedByThisMap = false := rfl
example : canonicalBoundary.pythonExecutionCountsAsLeanKernelProof = false := rfl

end Integration.TetracodeE8ExplicitMapRegression
