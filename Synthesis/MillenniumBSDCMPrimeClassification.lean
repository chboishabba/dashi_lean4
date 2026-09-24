import Synthesis.MillenniumBSDCMPrimeWitness
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# Exhaustive prime-level CM case split for E : y^2 = x^3 - x

For every prime, this file isolates the bad prime 2 and classifies every odd
prime into the two CM residue classes modulo four.  Split primes carry an
actual sum-of-two-squares witness.

This still does not choose the primary Gaussian associate/sign needed for the
literal signed Frobenius trace.
-/

namespace Synthesis.Millennium.BSD

inductive PrimeCMCase (p : ℕ) : Type where
  | badTwo (h : p = 2)
  | split (hmod : p % 4 = 1) (witness : SplitPrimeWitness p)
  | inert (hmod : p % 4 = 3)

theorem primeCMCase_exists {p : ℕ} (hp : p.Prime) :
    Nonempty (PrimeCMCase p) := by
  rcases hp.eq_two_or_odd with hp2 | hodd
  · exact ⟨PrimeCMCase.badTwo hp2⟩
  · rcases (Nat.odd_mod_four_iff.mp hodd) with h1 | h3
    · obtain ⟨w⟩ := splitPrimeWitness_of_mod_four_eq_one hp h1
      exact ⟨PrimeCMCase.split h1 w⟩
    · exact ⟨PrimeCMCase.inert h3⟩

theorem oddPrimeCMCase_exists {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ h : p % 4 = 1 ∨ p % 4 = 3,
      match h with
      | Or.inl h1 => Nonempty (SplitPrimeWitness p)
      | Or.inr _ => True := by
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact (hp2 h).elim
    · exact h
  rcases (Nat.odd_mod_four_iff.mp hodd) with h1 | h3
  · refine ⟨Or.inl h1, ?_⟩
    exact splitPrimeWitness_of_mod_four_eq_one hp h1
  · exact ⟨Or.inr h3, trivial⟩

def cmMagnitudeOfCase {p : ℕ} : PrimeCMCase p → Option ℕ
  | .badTwo _ => none
  | .split _ witness => some (cmMagnitude witness)
  | .inert _ => some 0

theorem split_case_doubled_norm
    {p : ℕ} {hmod : p % 4 = 1}
    (w : SplitPrimeWitness p) :
    cmMagnitude w ^ 2 + cmCompanion w ^ 2 = 4 * p :=
  doubled_norm_identity w

theorem inert_case_magnitude_zero
    {p : ℕ} (hmod : p % 4 = 3) :
    cmMagnitudeOfCase (PrimeCMCase.inert hmod) = some 0 := rfl

end Synthesis.Millennium.BSD
