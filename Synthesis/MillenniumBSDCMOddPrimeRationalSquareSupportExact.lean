import Synthesis.MillenniumBSDCMOddPrimeLocalSecondParityExact
import Synthesis.MillenniumBSDCMAllPrimeRationalSquareSupportExact
import Synthesis.MillenniumBSDSquareClassGroups
import Mathlib.Tactic

/-!
# BSD: actual Q*/Q*² support away from 2

The original rational square-class quotient admits exactly four possible
classes with even valuations at every odd prime:
[1], [-1], [2], [-2].

Proof: If v2(a) is even, apply the original all-prime rational square
factorization theorem directly. If it is odd, multiply by 2, use the
actual padicValRat valuation formula, the p!=2 unit fact, and the
same rational square factorization theorem. Cancel [2] using the
already-proved exponent-two group law.

No new quotient carrier or synthetic Selmer object. Source-written;
pinned local Lean kernel still pending.
-/

namespace Synthesis.Millennium.BSD

theorem cmRationalSquareClass_fourSupport_of_oddPrimeEven
    (a : NonzeroRat)
    (hodd :
      ∀ p : ℕ, Nat.Prime p → p ≠ 2 →
        Even (padicValRat p (a : ℚ))) :
    squareClassOf a = squareClassOf oneNZ ∨
    squareClassOf a = squareClassOf negOneNZ ∨
    squareClassOf a = squareClassOf twoNZ ∨
    squareClassOf a = squareClassOf negTwoNZ := by
  by_cases hev2 : Even (padicValRat 2 (a : ℚ))
  · have hall :
        ∀ p : ℕ, Nat.Prime p →
          Even (padicValRat p (a : ℚ)) := by
      intro p hp
      by_cases h : p = 2
      · simpa [h] using hev2
      · exact hodd p hp h
    rcases cmRationalSquareClass_one_or_negOne_of_allPrimeEven
      a hall with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · have htwisted :
        ∀ p : ℕ, Nat.Prime p →
          Even (padicValRat p ((a : ℚ) * 2)) := by
      intro p hp
      letI : Fact p.Prime := ⟨hp⟩
      have hmul :
          padicValRat p ((a : ℚ) * 2) =
            padicValRat p (a : ℚ) + padicValRat p (2 : ℚ) :=
        padicValRat.mul a.property (by norm_num)
      by_cases h : p = 2
      · subst p
        have htwo :
            padicValRat 2 (2 : ℚ) = 1 :=
          padicValRat.self (by norm_num : 1 < 2)
        rw [hmul, htwo]
        omega
      · have htwo :
            padicValRat p (2 : ℚ) = 0 := by
          have hv := cmQpOddValuation_two_zero (p := p) h
          change (((2 : ℚ) : ℚ_[p]).valuation) = 0 at hv
          simpa only [Padic.valuation_ratCast] using hv
        rw [hmul, htwo]
        simpa using hodd p hp h
    let b : NonzeroRat := nzRatMul a twoNZ
    have hbEven :
        ∀ p : ℕ, Nat.Prime p →
          Even (padicValRat p (b : ℚ)) := by
      intro p hp
      simpa [b, nzRatMul, twoNZ] using htwisted p hp
    have hmul :
        squareClassOf b =
          squareClassOf a * squareClassOf twoNZ := by
      exact squareClassOf_mul a twoNZ
    have hcancel :
        squareClassOf a =
          (squareClassOf a * squareClassOf twoNZ) *
            squareClassOf twoNZ := by
      rw [mul_assoc, ratSquareClass_sq_eq_one, mul_one]
    have hOne :
        squareClassOf oneNZ = (1 : RatSquareClass) := rfl
    have hNegTwo :
        squareClassOf negOneNZ * squareClassOf twoNZ =
          squareClassOf negTwoNZ := by
      rw [← squareClassOf_mul]
      apply Quotient.sound
      apply squareRel_of_eq
      apply Subtype.ext
      norm_num [nzRatMul, negOneNZ, twoNZ, negTwoNZ]
    rcases cmRationalSquareClass_one_or_negOne_of_allPrimeEven
      b hbEven with h | h
    · right; right; left
      calc
        squareClassOf a =
            (squareClassOf a * squareClassOf twoNZ) *
              squareClassOf twoNZ := hcancel
        _ = squareClassOf oneNZ * squareClassOf twoNZ := by
          rw [← hmul, h]
        _ = squareClassOf twoNZ := by rw [hOne, one_mul]
    · right; right; right
      calc
        squareClassOf a =
            (squareClassOf a * squareClassOf twoNZ) *
              squareClassOf twoNZ := hcancel
        _ = squareClassOf negOneNZ * squareClassOf twoNZ := by
          rw [← hmul, h]
        _ = squareClassOf negTwoNZ := hNegTwo

end Synthesis.Millennium.BSD
