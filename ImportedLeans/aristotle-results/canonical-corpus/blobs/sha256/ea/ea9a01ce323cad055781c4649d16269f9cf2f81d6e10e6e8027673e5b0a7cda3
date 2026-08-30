import Mathlib
import RequestProject.Tesla369

/-!
# Sieving by 2 and 3: two primes already cover two thirds of the integers

This file makes precise the observation that the very first two primes already do most of the
work of the sieve of Eratosthenes: crossing out the multiples of `2` and of `3` removes exactly
`4` of every `6` consecutive integers, i.e. a density of `2/3`, and every prime beyond `3` must
live in one of the two surviving classes `±1 mod 6`.

Note that `6 = 2 · 3` is the modulus that appears, and `9 = 3 ^ 2` is the modulus governing
digital roots: the "3, 6, 9" of `RequestProject.Tesla369` is the same arithmetic seen through the
primes `2` and `3`.
-/

namespace Sieve23

/-- The residues mod `6` killed by the primes `2` and `3`. -/
def sieved : Finset ℕ := (Finset.range 6).filter (fun r => 2 ∣ r ∨ 3 ∣ r)

/-- The residues mod `6` that survive sieving by `2` and `3`. -/
def survivors : Finset ℕ := (Finset.range 6).filter (fun r => ¬ (2 ∣ r ∨ 3 ∣ r))

theorem sieved_eq : sieved = {0, 2, 3, 4} := by decide

theorem survivors_eq : survivors = {1, 5} := by decide

/-- Four out of every six residues are removed: density `2/3`. -/
theorem sieved_card : sieved.card = 4 := by decide

/-- Only two out of every six residues survive: density `1/3`. -/
theorem survivors_card : survivors.card = 2 := by decide

/-- Membership in the sieved set depends only on the residue mod `6`. -/
theorem dvd_two_or_three_iff (n : ℕ) : (2 ∣ n ∨ 3 ∣ n) ↔ (2 ∣ n % 6 ∨ 3 ∣ n % 6) := by
  omega

/-- **Exact coverage.** Among the first `6 * k` natural numbers, exactly `4 * k` are divisible by
`2` or by `3`. -/
theorem card_sieved_range (k : ℕ) :
    ((Finset.range (6 * k)).filter (fun n => 2 ∣ n ∨ 3 ∣ n)).card = 4 * k := by
  induction k with
  | zero => simp
  | succ m ih =>
      have hrange : Finset.range (6 * (m + 1)) =
          Finset.range (6 * m) ∪ (Finset.Ico (6 * m) (6 * m + 6)) := by
        have h6 : 6 * (m + 1) = 6 * m + 6 := by ring
        rw [h6, Finset.range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (by omega)]
      have hdisj : Disjoint ((Finset.range (6 * m)).filter (fun n => 2 ∣ n ∨ 3 ∣ n))
          ((Finset.Ico (6 * m) (6 * m + 6)).filter (fun n => 2 ∣ n ∨ 3 ∣ n)) := by
        refine Finset.disjoint_left.mpr ?_
        intro x hx hx'
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx hx'
        omega
      rw [hrange, Finset.filter_union, Finset.card_union_of_disjoint hdisj, ih]
      have hblock : ((Finset.Ico (6 * m) (6 * m + 6)).filter (fun n => 2 ∣ n ∨ 3 ∣ n)).card = 4 := by
        have himg : Finset.Ico (6 * m) (6 * m + 6) =
            (Finset.range 6).image (fun r => 6 * m + r) := by
          ext x
          simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
          constructor
          · rintro ⟨h1, h2⟩; exact ⟨x - 6 * m, by omega, by omega⟩
          · rintro ⟨r, hr, rfl⟩; omega
        rw [himg, Finset.filter_image,
          Finset.card_image_of_injective _ (add_right_injective (6 * m))]
        have : (Finset.range 6).filter (fun r => 2 ∣ 6 * m + r ∨ 3 ∣ 6 * m + r) =
            (Finset.range 6).filter (fun r => 2 ∣ r ∨ 3 ∣ r) := by
          apply Finset.filter_congr
          intro r _
          constructor
          · rintro (h | h) <;> [left; right] <;> omega
          · rintro (h | h) <;> [left; right] <;> omega
        rw [this]
        exact sieved_card
      rw [hblock]
      ring

/-- **Every prime past `3` hides in the two surviving classes** `1` and `5` mod `6`. -/
theorem prime_mod_six {p : ℕ} (hp : p.Prime) (h3 : 3 < p) : p % 6 = 1 ∨ p % 6 = 5 := by
  have h2 : ¬ (2 ∣ p) := fun h => by
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp 2 h) with h | h <;> omega
  have h3' : ¬ (3 ∣ p) := fun h => by
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp 3 h) with h | h <;> omega
  omega

/-- Conversely the surviving classes are exactly the residues coprime to `6`, and there are
`φ(6) = 2` of them. -/
theorem totient_six : Nat.totient 6 = 2 := by decide

/-- The two survivors are `±1 mod 6`. -/
theorem survivors_symmetric : survivors = {1, 6 - 1} := by decide

/-- **Bridge to the digital-root trinity.**  Since a prime `p > 3` is not divisible by `3`, its
digital root avoids `3, 6, 9`: it is one of `1, 2, 4, 5, 7, 8`. -/
theorem prime_digitalRoot {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    Tesla369.digitalRoot p ∈ ({1, 2, 4, 5, 7, 8} : Finset ℕ) := by
  have hpos : 0 < p := by omega
  have hnot : Tesla369.digitalRoot p ∉ Tesla369.trinity := by
    rw [Tesla369.digitalRoot_mem_trinity_iff hpos]
    intro h
    rcases hp.eq_one_or_self_of_dvd 3 h with h | h <;> omega
  have h1 := Tesla369.digitalRoot_pos hpos
  have h2 := Tesla369.digitalRoot_le_nine p
  simp only [Tesla369.trinity, Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

end Sieve23
