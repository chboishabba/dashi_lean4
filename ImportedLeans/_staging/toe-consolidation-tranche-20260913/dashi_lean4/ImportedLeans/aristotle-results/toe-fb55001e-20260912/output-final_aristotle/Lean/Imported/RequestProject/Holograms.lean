import Mathlib

/-!
# Holograms: Mathematical foundations for the Aristo Dual-Atlas

This file collects the *proven mathematical foundations* on which both the primal
and the dual coordinate atlases rest.

The central object is the order of the Monster sporadic simple group `𝕄`,
whose prime factorisation is

  `|𝕄| = 2^46 · 3^20 · 5^9 · 7^6 · 11^2 · 13^3 · 17 · 19 · 23 · 29 · 31 · 41 · 47 · 59 · 71`.

We record:

* `monsterOrder` — the order itself.
* `monster_divisor_count` — its number of divisors equals `424 488 960`.
* `monster_threeadic_depth` — the 3-adic valuation of any divisor is `≤ 20`.
* `divisors_partition_mod` — divisors partition by residue (prime-signature partition).
* `dualizePair_involutive` — base/exponent swap `p^e ↦ e^p` is an involution.
-/

namespace Holograms

/-- The order of the Monster sporadic simple group, given by its prime factorisation. -/
def monsterOrder : ℕ :=
  2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3
    * 17 * 19 * 23 * 29 * 31 * 41 * 47 * 59 * 71

/-
The number of divisors of `|𝕄|` is `424 488 960 = 47·21·10·7·3·4·2^9`.
-/
theorem monster_divisor_count : monsterOrder.divisors.card = 424488960 := by
  -- Apply the formula for the number of divisors of a product of prime powers.
  have h_divisors_formula : ∀ {n : ℕ}, n ≠ 0 → (Nat.divisors n).card = (∏ p ∈ Nat.primeFactors n, (Nat.factorization n p + 1)) := by
    grind +suggestions;
  rw [ h_divisors_formula ] <;> native_decide;

/-
3-adic depth bound: every divisor of `|𝕄|` has 3-adic valuation at most `20`,
since `3^20 ∥ |𝕄|`.
-/
theorem monster_threeadic_depth (d : ℕ) (hd : d ∣ monsterOrder) :
    d.factorization 3 ≤ 20 := by
  have h_factorization : d.factorization ≤ (monsterOrder.factorization) := by
    exact Nat.factorization_le_iff_dvd ( by rintro rfl; exact absurd hd ( by native_decide ) ) ( by native_decide ) |>.2 hd;
  exact le_trans ( h_factorization 3 ) ( by native_decide )

/-- Prime-signature partition: for any modulus `m > 0`, the divisors of `n` are
partitioned by their residue modulo `m`.  Specialising `m` to `5, 7, 11, 13`
yields the harmonic cell classification. -/
theorem divisors_partition_mod (n m : ℕ) (hm : 0 < m) :
    n.divisors = (Finset.range m).biUnion (fun r => n.divisors.filter (· % m = r)) := by
  ext d
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter]
  constructor
  · intro hd; exact ⟨d % m, Nat.mod_lt _ hm, hd, rfl⟩
  · rintro ⟨r, _, hd, _⟩; exact hd

/-- The exponent–base involution `p^e ↦ e^p`, modelled on pairs `(p, e)` as the
swap `(p, e) ↦ (e, p)`. -/
def dualizePair : ℕ × ℕ → ℕ × ℕ := Prod.swap

/-- Validity of the dual atlas: the exponent–base involution is an involution
(applying it twice is the identity), hence a bijection preserving the structure. -/
theorem dualizePair_involutive : Function.Involutive dualizePair := by
  intro x; simp [dualizePair]

/-- The dualization is in particular a bijection of `ℕ × ℕ`. -/
theorem dualizePair_bijective : Function.Bijective dualizePair :=
  dualizePair_involutive.bijective

end Holograms