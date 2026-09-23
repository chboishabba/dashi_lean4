import Synthesis.MillenniumBSDCMPrimeClassification
import Synthesis.MillenniumBSDCMSplitPrimeSignReduction
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic

/-!
# Canonical odd/even representation of split CM primes

Fermat two-squares already gives p = u² + v² for p ≡ 1 mod 4.
Because p is odd, exactly one coordinate is odd and the other even.  Reorder
the pair and write them as 2r+1 and 2s.  This produces exactly the witness
shape consumed by the signed split-prime Frobenius theorem.

The theorem is elementary bookkeeping, but paying it removes a hidden
existence premise from the CM/Jacobi prime comparison.
-/

namespace Synthesis.Millennium.BSD

structure SplitPrimeCanonicalWitness (p : ℕ) where
  r : ℕ
  s : ℕ
  normExact : p = (2 * r + 1) ^ 2 + 4 * s ^ 2

private theorem odd_ne_even_nat {n : ℕ} (ho : Odd n) (he : Even n) : False := by
  rcases ho with ⟨a, ha⟩
  rcases he with ⟨b, hb⟩
  omega

private theorem odd_of_sq_add_sq_odd_left
    {u v : ℕ} (hsum : Odd (u ^ 2 + v ^ 2)) (hv : Even v) :
    Odd u := by
  rcases Nat.even_or_odd u with hu | hu
  · have hu2 : Even (u ^ 2) := hu.pow_of_ne_zero (by norm_num)
    have hv2 : Even (v ^ 2) := hv.pow_of_ne_zero (by norm_num)
    exact (odd_ne_even_nat hsum (hu2.add hv2)).elim
  · exact hu

private theorem odd_of_sq_add_sq_odd_right
    {u v : ℕ} (hsum : Odd (u ^ 2 + v ^ 2)) (hu : Even u) :
    Odd v := by
  rcases Nat.even_or_odd v with hv | hv
  · have hu2 : Even (u ^ 2) := hu.pow_of_ne_zero (by norm_num)
    have hv2 : Even (v ^ 2) := hv.pow_of_ne_zero (by norm_num)
    exact (odd_ne_even_nat hsum (hu2.add hv2)).elim
  · exact hv

theorem splitPrimeCanonicalWitness_of_mod_four_eq_one
    {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1) :
    Nonempty (SplitPrimeCanonicalWitness p) := by
  obtain ⟨w⟩ := splitPrimeWitness_of_mod_four_eq_one hp hmod
  have hpOdd : Odd p := by
    exact (Nat.odd_iff.mpr (Nat.odd_of_mod_four_eq_one hmod))
  have hsumOdd : Odd (w.u ^ 2 + w.v ^ 2) := by
    simpa [w.normExact] using hpOdd
  rcases Nat.even_or_odd w.u with hu | hu
  · have hv : Odd w.v := odd_of_sq_add_sq_odd_right hsumOdd hu
    rcases hu with ⟨s, hs⟩
    rcases hv with ⟨r, hr⟩
    refine ⟨⟨r, s, ?_⟩⟩
    rw [w.normExact, hr, hs]
    simp only [two_mul]
    ring
  · rcases Nat.even_or_odd w.v with hv | hv
    · rcases hu with ⟨r, hr⟩
      rcases hv with ⟨s, hs⟩
      refine ⟨⟨r, s, ?_⟩⟩
      rw [w.normExact, hr, hs]
      simp only [two_mul]
      ring
    · have hu2 : Odd (w.u ^ 2) := hu.pow
      have hv2 : Odd (w.v ^ 2) := hv.pow
      have heven : Even (w.u ^ 2 + w.v ^ 2) := hu2.add_odd hv2
      exact (odd_ne_even_nat hsumOdd heven).elim

/-- The paid split-prime sign theorem can now be invoked from residue-class
information alone, with no externally supplied sum-of-two-squares witness. -/
theorem split_frobenius_signed_exists
    {p : ℕ} (hp : p.Prime) (hmod : p % 4 = 1) :
    ∃ r s : ℕ,
      p = (2 * r + 1) ^ 2 + 4 * s ^ 2 ∧
      frobeniusCoefficient p =
        2 * ((-1 : ℤ) ^ (r + s)) * (2 * r + 1) := by
  obtain ⟨w⟩ := splitPrimeCanonicalWitness_of_mod_four_eq_one hp hmod
  refine ⟨w.r, w.s, w.normExact, ?_⟩
  exact split_frobenius_signed hp w.normExact hmod

end Synthesis.Millennium.BSD
