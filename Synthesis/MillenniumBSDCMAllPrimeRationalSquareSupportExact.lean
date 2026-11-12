import Synthesis.MillenniumBSDPinnedSquareCriterionV428Exact
import Synthesis.MillenniumBSDRationalSquareClassQuotient
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-!
# Selected BSD: global rational square-class unit support from all-prime parity

This is a genuine classification theorem on the original RatSquareClass
quotient and its original SquareRel, using Mathlib's
Rat.isSquare_iff_even_factorization.

If all prime valuations of a nonzero rational are even, then its
square class is [1] or [-1], with the sign determining which.
No invented square-class carrier or uninstantiated is-square axiom.

The missing producer is to prove all-prime even valuation for the
first x-T coordinate of each ORIGINAL explicit Selmer class, by
generalizing the already proved Q2 local-image result to arbitrary p.
This module supplies the final rational factorization consumer.
Source-written; exact-head local Lean kernel pending.
-/

namespace Synthesis.Millennium.BSD

/-- A nonzero rational with even valuation at every prime has actual
square class [1] or [-1] in the repository's original quotient. -/
theorem cmRationalSquareClass_one_or_negOne_of_allPrimeEven
    (a : NonzeroRat)
    (heven :
      ∀ p : ℕ, Nat.Prime p →
        Even (padicValRat p (a : ℚ))) :
    squareClassOf a = squareClassOf oneNZ ∨
      squareClassOf a = squareClassOf negOneNZ := by
  by_cases ha : 0 ≤ (a : ℚ)
  · have hsq : IsSquare (a : ℚ) :=
      (Rat.isSquare_iff_even_factorization).2 ⟨ha, heven⟩
    rcases hsq with ⟨b, hb⟩
    have hbne : b ≠ 0 := by
      intro hzero
      apply a.property
      nlinarith [hb]
    left
    apply Quotient.sound
    refine ⟨oneNZ, ⟨b, hbne⟩, ?_⟩
    change (a : ℚ) * (1 : ℚ) ^ 2 = (1 : ℚ) * b ^ 2
    nlinarith [hb]
  · have haneg : 0 ≤ -(a : ℚ) := by linarith
    have hEvenNeg :
        ∀ p : ℕ, Nat.Prime p →
          Even (padicValRat p (-(a : ℚ))) := by
      intro p hp
      simpa [padicValRat.neg] using heven p hp
    have hsq : IsSquare (-(a : ℚ)) :=
      cmPinnedRatSquare_of_nonneg_even_padicVal (-(a : ℚ)) haneg hEvenNeg
    rcases hsq with ⟨b, hb⟩
    have hbne : b ≠ 0 := by
      intro hzero
      apply a.property
      nlinarith [hb]
    right
    apply Quotient.sound
    refine ⟨oneNZ, ⟨b, hbne⟩, ?_⟩
    change (a : ℚ) * (1 : ℚ) ^ 2 = (-1 : ℚ) * b ^ 2
    nlinarith [hb]

end Synthesis.Millennium.BSD
