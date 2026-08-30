import Mathlib
import AgdaMirror.GodelLattice
import AgdaMirror.Vec15Order
import AgdaMirror.Vec15Descriptive

/-!
# Lean mirror of `DASHI/Statistics/Vec15Inference.agda` (genuine, fully proved)

A minimal concrete inference / modeling surface for the 15-prime carrier.  The
deterministic core stays small (a Boolean decision surface, a confidence-interval
scaffold, baseline test results built from the descriptive summaries) but is
faithfully transcribed.  On top of the faithful mirror we prove genuine
theorems: the confidence intervals built here are always *valid*
(`lower ≤ upper`), the paired test result is always interval-consistent, and the
reject / fail decision bits are genuinely complementary.
-/

namespace AgdaMirror.Vec15Inference

open AgdaMirror.GodelLattice
open AgdaMirror.Vec15Order
open AgdaMirror.Vec15Descriptive

/-- A hypothesis-test decision. -/
inductive Decision where
  | reject : Decision
  | failToReject : Decision
deriving DecidableEq

/-- A null/alternative hypothesis tag. -/
inductive HypothesisTag where
  | nullTag : HypothesisTag
  | alternativeTag : HypothesisTag
deriving DecidableEq

/-- A pair of hypothesis tags. -/
structure Hypothesis where
  null : HypothesisTag
  alternative : HypothesisTag

/-- A confidence interval over `Nat`. -/
structure ConfidenceInterval where
  lower : Nat
  upper : Nat

/-- A fully-recorded test result. -/
structure TestResult where
  hypothesis : Hypothesis
  statistic : Nat
  pValue : Nat
  decision : Decision
  interval : ConfidenceInterval
  rejectBit : Bool
  failBit : Bool
  intervalConsistent : Bool

/-! ### Cheap deterministic helpers -/

/-- Boolean `≤` on `Nat`. -/
def leqNat : Nat → Nat → Bool
  | 0, _ => true
  | _+1, 0 => false
  | m+1, n+1 => leqNat m n

/-- `leqNat` agrees with the decidable `≤`. -/
theorem leqNat_iff (m n : Nat) : leqNat m n = true ↔ m ≤ n := by
  induction m generalizing n with
  | zero => simp [leqNat]
  | succ k ih =>
    cases n with
    | zero => simp [leqNat]
    | succ j => simpa [leqNat, Nat.succ_le_succ_iff] using ih j

/-- Boolean conjunction (matching the Agda `andBool`). -/
def andBool : Bool → Bool → Bool
  | true, true => true
  | _, _ => false

@[simp] theorem andBool_eq (a b : Bool) : andBool a b = (a && b) := by
  cases a <;> cases b <;> rfl

/-- Boolean negation. -/
def boolNot : Bool → Bool
  | true => false
  | false => true

/-- Is a decision a rejection? -/
def decisionIsReject : Decision → Bool
  | .reject => true
  | .failToReject => false

/-- Is a decision a failure-to-reject? -/
def decisionIsFail (d : Decision) : Bool := boolNot (decisionIsReject d)

/-- The reject / fail bits of any decision are complementary. -/
theorem decision_bits_complementary (d : Decision) :
    decisionIsFail d = boolNot (decisionIsReject d) := rfl

/-- A confidence interval anchored at `0`, scaled by the max + level. -/
def confidenceInterval15 (level : Nat) (xs : PrimeCarrier15) : ConfidenceInterval :=
  ⟨0, max15 xs + level⟩

/-- Does `x` lie in the interval? -/
def confidenceIntervalContains (x : Nat) (interval : ConfidenceInterval) : Bool :=
  if leqNat interval.lower x then leqNat x interval.upper else false

/-- Is the interval well-formed (`lower ≤ upper`)? -/
def confidenceIntervalValid (interval : ConfidenceInterval) : Bool :=
  leqNat interval.lower interval.upper

/-- The interval scaffold built by `confidenceInterval15` is always valid. -/
theorem confidenceInterval15_valid (level : Nat) (xs : PrimeCarrier15) :
    confidenceIntervalValid (confidenceInterval15 level xs) = true := by
  simp [confidenceIntervalValid, confidenceInterval15, leqNat]

/-- The baseline reject/fail decision from the descriptive summaries. -/
def baselineDecision (xs : PrimeCarrier15) : Decision :=
  if leqNat (sum15 xs) (countNonZero15 xs) then Decision.failToReject else Decision.reject

/-- The baseline test result. -/
def baselineTestResult (h : Hypothesis) (xs : PrimeCarrier15) : TestResult :=
  let statistic := sum15 xs
  let pValue := countNonZero15 xs
  let interval := confidenceInterval15 0 xs
  let decision := baselineDecision xs
  { hypothesis := h
    statistic := statistic
    pValue := pValue
    decision := decision
    interval := interval
    rejectBit := decisionIsReject decision
    failBit := decisionIsFail decision
    intervalConsistent :=
      andBool (confidenceIntervalValid interval)
        (confidenceIntervalContains statistic interval) }

/-- The baseline result's reject and fail bits are complementary. -/
theorem baselineTestResult_bits (h : Hypothesis) (xs : PrimeCarrier15) :
    (baselineTestResult h xs).failBit = boolNot (baselineTestResult h xs).rejectBit := rfl

/-! ### Paired surface -/

/-- Combined statistic of a pair. -/
def pairStatistic (xs ys : PrimeCarrier15) : Nat := sum15 xs + sum15 ys

/-- Combined p-value of a pair. -/
def pairPValue (xs ys : PrimeCarrier15) : Nat := countNonZero15 xs + countNonZero15 ys

/-- Combined support of a pair. -/
def pairSupport (xs ys : PrimeCarrier15) : Nat := countNonZero15 xs + countNonZero15 ys

/-- Combined contrast of a pair. -/
def pairContrast (xs ys : PrimeCarrier15) : Nat := pairStatistic xs ys + pairSupport xs ys

/-- Paired reject/fail decision. -/
def pairDecision (xs ys : PrimeCarrier15) : Decision :=
  if leqNat (pairStatistic xs ys) (pairPValue xs ys) then Decision.failToReject
  else Decision.reject

/-- Paired confidence interval: `[0, stat + pValue]`. -/
def pairInterval (xs ys : PrimeCarrier15) : ConfidenceInterval :=
  ⟨0, pairStatistic xs ys + pairPValue xs ys⟩

/-- Paired test result. -/
def pairTestResult (h : Hypothesis) (xs ys : PrimeCarrier15) : TestResult :=
  let statistic := pairStatistic xs ys
  let pValue := pairPValue xs ys
  let interval := pairInterval xs ys
  let decision := pairDecision xs ys
  { hypothesis := h
    statistic := statistic
    pValue := pValue
    decision := decision
    interval := interval
    rejectBit := decisionIsReject decision
    failBit := decisionIsFail decision
    intervalConsistent :=
      andBool (confidenceIntervalValid interval)
        (confidenceIntervalContains statistic interval) }

/-- The paired interval is always valid. -/
theorem pairInterval_valid (xs ys : PrimeCarrier15) :
    confidenceIntervalValid (pairInterval xs ys) = true := by
  simp [confidenceIntervalValid, pairInterval, leqNat]

/-- The paired interval always contains its own statistic (since the upper bound
is `stat + pValue ≥ stat`). -/
theorem pairInterval_contains_statistic (xs ys : PrimeCarrier15) :
    confidenceIntervalContains (pairStatistic xs ys) (pairInterval xs ys) = true := by
  simp only [confidenceIntervalContains, pairInterval]
  rw [if_pos (by simp [leqNat])]
  rw [leqNat_iff]
  exact Nat.le_add_right _ _

/-- Therefore the paired test result is always interval-consistent. -/
theorem pairTestResult_intervalConsistent (h : Hypothesis) (xs ys : PrimeCarrier15) :
    (pairTestResult h xs ys).intervalConsistent = true := by
  have h1 := pairInterval_valid xs ys
  have h2 := pairInterval_contains_statistic xs ys
  simp only [pairTestResult, andBool_eq, h1, h2, Bool.and_self]

/-- The shared model hypothesis. -/
def modelHypothesis : Hypothesis := ⟨HypothesisTag.nullTag, HypothesisTag.alternativeTag⟩

/-! ### Named operators (reusing the baseline / paired semantics) -/

def anova15 : PrimeCarrier15 → TestResult := baselineTestResult modelHypothesis
def chiSquared15 : PrimeCarrier15 → TestResult := baselineTestResult modelHypothesis
def tTest15 (xs ys : PrimeCarrier15) : TestResult := pairTestResult modelHypothesis xs ys
def mannWhitney15 (xs ys : PrimeCarrier15) : TestResult := pairTestResult modelHypothesis xs ys
def kruskalWallis15 : PrimeCarrier15 → TestResult := baselineTestResult modelHypothesis

/-- The t-test is always interval-consistent. -/
theorem tTest15_intervalConsistent (xs ys : PrimeCarrier15) :
    (tTest15 xs ys).intervalConsistent = true :=
  pairTestResult_intervalConsistent _ xs ys

end AgdaMirror.Vec15Inference
