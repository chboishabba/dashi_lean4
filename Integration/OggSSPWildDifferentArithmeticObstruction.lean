import Mathlib

/-!
# Wild different versus exceptional Monster gaps: arithmetic obstruction

Source and ownership:
* Duncan--Swisher provide the monstrous-exponent arithmetic (their formula is
  proved for p > 3); the exceptional continuation gaps are 10 and 2.
* Kobin--Zureick-Brown study wild stacky modular forms. The raw local numbers
  14 and 7 are separately recorded upstream in the Agda comparison.
* This Lean file proves **only** the finite arithmetic obstruction that these
  recorded raw numbers cannot equal the exceptional gaps.

No source is credited with an additive Monster wild-stack formula; neither a
source-native valuation observable nor an actual correction mechanism is
constructed here.
-/

namespace Integration.OggSSPWildDifferentArithmeticObstruction

inductive SmallPrime
  | two | three
  deriving DecidableEq, Repr, Fintype

def rawDifferent : SmallPrime → Nat
  | .two => 14
  | .three => 7

def exceptionalGap : SmallPrime → Nat
  | .two => 10
  | .three => 2

/-- The *unpaid arithmetic offset* is not asserted to be an arithmetic
    geometric correction. -/
def unpaidOffset : SmallPrime → Nat
  | .two => 4
  | .three => 5

theorem raw_different_split (p : SmallPrime) :
    rawDifferent p = exceptionalGap p + unpaidOffset p := by
  cases p <;> decide

theorem raw_different_ne_exceptional_gap (p : SmallPrime) :
    rawDifferent p ≠ exceptionalGap p := by
  cases p <;> decide

/-- Hypothesis that the raw wild different IS the missing exponent correction. -/
structure RawIdentityCorrection where
  predicts : ∀ p : SmallPrime, rawDifferent p = exceptionalGap p

theorem no_raw_identity_correction : ¬ Nonempty RawIdentityCorrection := by
  rintro ⟨candidate⟩
  exact raw_different_ne_exceptional_gap .two (candidate.predicts .two)

/-- A mechanism needs a genuine source observable and a separately identified
    link to the exceptional exponent valuation. Its mere abstract existence is
    not derived from two numerically matching counts. -/
structure CandidateCorrection (Observable : Type) where
  sourceObservable : SmallPrime → Observable
  valuationContribution : Observable → Nat
  matchesGap : ∀ p, valuationContribution (sourceObservable p) = exceptionalGap p
  sourceRecognition : Prop

/-- The raw observed coefficient cannot instantiate the proposed mechanism
    with an identity valuation contribution. -/
theorem no_identity_observable_candidate :
    ¬ ∃ (candidate : CandidateCorrection Nat),
      (∀ p, candidate.sourceObservable p = rawDifferent p) ∧
      (∀ n, candidate.valuationContribution n = n) := by
  rintro ⟨candidate, fromRaw, contributionIsIdentity⟩
  have h : rawDifferent .two = exceptionalGap .two := by
    calc
      rawDifferent .two = candidate.sourceObservable .two := (fromRaw .two).symm
      _ = candidate.valuationContribution (candidate.sourceObservable .two) :=
        (contributionIsIdentity (candidate.sourceObservable .two)).symm
      _ = exceptionalGap .two := candidate.matchesGap .two
  exact raw_different_ne_exceptional_gap .two h

inductive ClaimOrigin
  | duncanSwisherArithmetic
  | kobinZureickBrownWildGeometry
  | repositoryCrossModuleArithmetic
  | openMechanism
  deriving DecidableEq, Repr

structure Boundary where
  exactP2Split : Bool
  exactP3Split : Bool
  rawIdentityRefuted : Bool
  actualStackToMonsterMechanismProved : Bool
  sourceRecognitionPaid : Bool
  deriving Repr

def canonicalBoundary : Boundary where
  exactP2Split := true
  exactP3Split := true
  rawIdentityRefuted := true
  actualStackToMonsterMechanismProved := false
  sourceRecognitionPaid := false

end Integration.OggSSPWildDifferentArithmeticObstruction
