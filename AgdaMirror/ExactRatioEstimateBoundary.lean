/-! Secondary mirror of DASHI.Interop.ExactRatioEstimateBoundary.
Arithmetic equivalence is not empirical estimation or model comparison. -/
namespace AgdaMirror.ExactRatioEstimateBoundary

structure PositiveDenominatorRatio where
  numerator : Nat
  denominatorPredecessor : Nat

def denominator (r : PositiveDenominatorRatio) : Nat :=
  r.denominatorPredecessor + 1

def RatioEquivalent (left right : PositiveDenominatorRatio) : Prop :=
  left.numerator * denominator right =
    right.numerator * denominator left

theorem ratioReflexive (r : PositiveDenominatorRatio) :
    RatioEquivalent r r := rfl

theorem ratioSymmetric (left right : PositiveDenominatorRatio)
    (h : RatioEquivalent left right) :
    RatioEquivalent right left := h.symm

theorem sameRepresentation (n d : Nat) :
    RatioEquivalent ⟨n, d⟩ ⟨n, d⟩ := rfl

end AgdaMirror.ExactRatioEstimateBoundary
