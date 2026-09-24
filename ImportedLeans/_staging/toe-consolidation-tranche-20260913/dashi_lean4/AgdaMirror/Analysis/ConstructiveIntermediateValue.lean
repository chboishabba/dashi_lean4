import Mathlib
import AgdaMirror.Analysis.ConcreteComplex

/-!
# Mirror of `DASHI/Analysis/ConstructiveIntermediateValue.agda`

Continuity witnesses, signs, and the intermediate-value operation remain
explicit authority fields.  The two assembly theorems merely consume those
fields; they do not assert an unconditional constructive IVT.
-/

namespace AgdaMirror.Analysis

/-- Constructive continuity data, left abstract exactly as in the Agda surface. -/
structure ContinuousOnInterval
    (R : ConstructedRealOps) (f : R.Real → R.Real) (left right : R.Real) where
  Modulus : Type
  modulus : Modulus
  ContinuityEstimate : Type
  continuityEstimate : ContinuityEstimate

/-- Imported constructive IVT authority.  `rootBetween` is an explicit field,
not a theorem claimed by this transcription. -/
structure IntermediateValueAuthority (R : ConstructedRealOps) where
  Nonnegative : R.Real → Prop
  Nonpositive : R.Real → Prop
  le : R.Real → R.Real → Prop
  rootBetween : ∀ (f : R.Real → R.Real) (left right : R.Real),
    le left right →
    ContinuousOnInterval R f left right →
    Nonpositive (f left) →
    Nonnegative (f right) →
    {root : R.Real // le left root ∧ le root right ∧ f root = R.zero}

/-- A finite sign-changing bracket for a shifted exponential. -/
structure ExponentialBracket
    (R : ConstructedRealOps) (I : IntermediateValueAuthority R)
    (shifted : R.Real → R.Real) where
  left : R.Real
  right : R.Real
  left_le_right : I.le left right
  continuous : ContinuousOnInterval R shifted left right
  leftNonpositive : I.Nonpositive (shifted left)
  rightNonnegative : I.Nonnegative (shifted right)

/-- Explicit range-and-continuity assumptions needed to derive positive
surjectivity from IVT. -/
structure ExponentialRangeAndContinuity
    (R : ConstructedRealOps) (I : IntermediateValueAuthority R)
    (exp : R.Real → R.Real) (Positive : R.Real → Prop) where
  shiftedExponential : R.Real → R.Real → R.Real
  shiftedZeroImpliesExpEquals : ∀ y x,
    shiftedExponential y x = R.zero → exp x = y
  bracket : ∀ y, Positive y → ExponentialBracket R I (shiftedExponential y)

/-- Conditional exponential surjectivity: the conclusion is proved from the
explicit IVT and bracketing authority fields. -/
theorem expOntoPositiveFromIVT
    {R : ConstructedRealOps}
    (I : IntermediateValueAuthority R)
    (exp : R.Real → R.Real)
    (Positive : R.Real → Prop)
    (A : ExponentialRangeAndContinuity R I exp Positive)
    (y : R.Real) (py : Positive y) :
    ∃ x, exp x = y := by
  let B := A.bracket y py
  obtain ⟨root, _, _, rootZero⟩ :=
    I.rootBetween (A.shiftedExponential y) B.left B.right
      B.left_le_right B.continuous B.leftNonpositive B.rightNonnegative
  exact ⟨root, A.shiftedZeroImpliesExpEquals y root rootZero⟩

/-- The first-positive-zero interface imported by the power-series layer. -/
structure FirstPositiveCosineZero
    (R : ConstructedRealOps) (cosine : R.Real → R.Real) where
  lt : R.Real → R.Real → Prop
  halfPi : R.Real
  halfPiPositive : lt R.zero halfPi
  cosineHalfPiZero : cosine halfPi = R.zero
  cosinePositiveBefore : ∀ x,
    lt R.zero x → lt x halfPi → lt R.zero (cosine x)

/-- The exact minimality authority needed to identify a zero as the first
positive cosine zero. -/
structure FirstZeroMinimality
    (R : ConstructedRealOps) (cosine : R.Real → R.Real) (halfPi : R.Real) where
  lt : R.Real → R.Real → Prop
  halfPiPositive : lt R.zero halfPi
  cosineHalfPiZero : cosine halfPi = R.zero
  cosinePositiveBefore : ∀ x,
    lt R.zero x → lt x halfPi → lt R.zero (cosine x)

/-- Pure packaging theorem: an explicit minimality witness supplies the
first-positive-zero interface. -/
def firstPositiveCosineZeroFromMinimality
    {R : ConstructedRealOps} {cosine : R.Real → R.Real} {halfPi : R.Real}
    (M : FirstZeroMinimality R cosine halfPi) :
    FirstPositiveCosineZero R cosine where
  lt := M.lt
  halfPi := halfPi
  halfPiPositive := M.halfPiPositive
  cosineHalfPiZero := M.cosineHalfPiZero
  cosinePositiveBefore := M.cosinePositiveBefore

end AgdaMirror.Analysis
