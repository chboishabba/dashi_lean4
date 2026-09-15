/-
# The R414 dual consumer: composition only after *both* receipts

## The consumer

`NSTriadKNSignedCancellationDualConsumerRound414Exact` freezes the shape

```agda
record DualSignedCancellationPayment (Time : Set) : Set₁ where
  field
    signedRemainderIntegral        : Nat → Time → ℚ
    criticalSize                   : Nat → Time → ℚ
    cutoffIndependentRemainderBound : Time → ℚ
    cutoffIndependentCriticalBound  : Time → ℚ
    remainderBound : ...
    criticalBound  : ...
```

together with the explicit Boolean disclaimer
`round414DoesNotAssumePackageAImpliesCriticalBarrier = true` and
`round414DualPaymentCurrentlyConstructed = false`.

This file replaces the Boolean disclaimer by theorems.

## What is proved

* `dualPayment_of_receipts` — the composition: an A1 receipt
  (`CommutatorOnlySpacetimeBudget568`) and an A2 receipt
  (`UniformSignedCriticalCeiling`) together construct the R414 dual payment,
  with the R568 quantity `4 ∫₀ᵀ globalForcingFull` as the signed remainder
  integral.  Both receipts are used; neither is optional.

* `a1_does_not_pay_a2` and `a2_does_not_pay_a1` — the non-collapse theorems.
  There are data for which the A1 record exists and the A2 record provably does
  not, and conversely.  Hence no proof of one payment can discharge the other
  at this interface: the Agda Boolean
  `round414DoesNotAssumePackageAImpliesCriticalBarrier` is now a proved
  statement about the interfaces themselves.

## Status

Consumer composition.  Sound but *unpaid*: neither A1 nor A2 is discharged
anywhere in this library, so no instance of `DualSignedCancellationPayment` is
constructed from thin air here.
-/
import NSUnforced.A1Budget568
import NSUnforced.A2CriticalCeiling

open MeasureTheory

noncomputable section

namespace DASHI.NS.Unforced

/-- The R414 dual payment over `ℝ`. -/
structure DualSignedCancellationPayment
    (signedRemainderIntegral criticalSize : ℕ → ℝ → ℝ) where
  /-- `cutoffIndependentRemainderBound`. -/
  remainderCeiling : ℝ → ℝ
  /-- `cutoffIndependentCriticalBound`. -/
  criticalCeiling : ℝ → ℝ
  /-- `remainderBound`. -/
  remainderBound : ∀ (N : ℕ) (T : ℝ), 0 ≤ T →
    signedRemainderIntegral N T ≤ remainderCeiling T
  /-- `criticalBound`. -/
  criticalBound : ∀ (N : ℕ) (T : ℝ), 0 ≤ T → criticalSize N T ≤ criticalCeiling T

/-- The R568 spacetime quantity, read as the R414 signed remainder integral. -/
def signedRemainderIntegral (globalForcingFull : ℕ → ℝ → ℝ) (N : ℕ) (T : ℝ) : ℝ :=
  4 * ∫ t in (0 : ℝ)..T, globalForcingFull N t

/-- **Composition.**  The dual consumer is constructed from the two receipts and
from nothing else. -/
def dualPayment_of_receipts {globalForcingFull criticalSize : ℕ → ℝ → ℝ}
    (a1 : CommutatorOnlySpacetimeBudget568 globalForcingFull)
    (a2 : UniformSignedCriticalCeiling criticalSize) :
    DualSignedCancellationPayment (signedRemainderIntegral globalForcingFull)
      criticalSize where
  remainderCeiling := a1.bound
  criticalCeiling := a2.ceiling
  remainderBound := a1.budget
  criticalBound := a2.bound

/-- **Non-collapse, first direction.**  A1 can hold while A2 fails. -/
theorem a1_does_not_pay_a2 :
    ∃ (G P : ℕ → ℝ → ℝ),
      Nonempty (CommutatorOnlySpacetimeBudget568 G) ∧
        ¬ Nonempty (UniformSignedCriticalCeiling P) := by
  refine ⟨fun _ _ => 0, fun N _ => (N : ℝ), ⟨⟨fun _ => 0, ?_⟩⟩, ?_⟩
  · intro N T _
    simp
  · rintro ⟨⟨ceil, hceil⟩⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (ceil 1)
    exact absurd (hceil n 1 zero_le_one) (not_le.mpr hn)

/-- **Non-collapse, second direction.**  A2 can hold while A1 fails. -/
theorem a2_does_not_pay_a1 :
    ∃ (G P : ℕ → ℝ → ℝ),
      Nonempty (UniformSignedCriticalCeiling P) ∧
        ¬ Nonempty (CommutatorOnlySpacetimeBudget568 G) := by
  refine ⟨fun N _ => (N : ℝ), fun _ _ => 0, ⟨⟨fun _ => 0, ?_⟩⟩, ?_⟩
  · intro N T _
    simp
  · rintro ⟨⟨bnd, hbnd⟩⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (bnd 1)
    have hint : (4 : ℝ) * ∫ _t in (0 : ℝ)..(1 : ℝ), (n : ℝ) = 4 * (n : ℝ) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, one_mul]
    have h := hbnd n 1 zero_le_one
    rw [hint] at h
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

end DASHI.NS.Unforced
