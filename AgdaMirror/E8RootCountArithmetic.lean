/-! Secondary mirror of DASHI.Algebra.Trit.E8RootCountArithmeticExact.
Candidate-count arithmetic is not a constructed E8 root enumeration. -/
namespace AgdaMirror.E8RootCountArithmetic

def coordinatePairs : Nat := 28
def signChoicesPerPair : Nat := 4
def integerChoiceCount : Nat := coordinatePairs * signChoicesPerPair
def evenParityHalfChoiceTarget : Nat := 128
def combinedChoiceCount : Nat :=
  integerChoiceCount + evenParityHalfChoiceTarget

theorem integerChoiceArithmetic : integerChoiceCount = 112 := rfl
theorem halfChoiceTargetArithmetic : evenParityHalfChoiceTarget = 128 := rfl
theorem combinedChoiceArithmetic : combinedChoiceCount = 240 := rfl

end AgdaMirror.E8RootCountArithmetic
