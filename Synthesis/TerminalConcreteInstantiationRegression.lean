import Synthesis.TerminalConcreteInstantiation

namespace Synthesis.TerminalConcreteInstantiationRegression

open Synthesis.TerminalConcreteInstantiation

example (k : ℕ) :
    (canonicalTerminalClosure k).rtReplacement.actualEntropy =
      (canonicalTerminalClosure k).rtReplacement.actualCutEntropy :=
  canonicalTerminalRT k

example (k : ℕ) :
    (canonicalTerminalReceipt k).einstein.Lambda = 0 := canonicalTerminalLambdaZero k

example : sourceModelInstantiationClosed = true := rfl
example : authorityInstantiationClosed = true := rfl
example : empiricalCalibrationClosedForDeclaredBenchmark = true := rfl
example : terminalResidualListEmptyForDeclaredBenchmark = true := rfl

end Synthesis.TerminalConcreteInstantiationRegression
