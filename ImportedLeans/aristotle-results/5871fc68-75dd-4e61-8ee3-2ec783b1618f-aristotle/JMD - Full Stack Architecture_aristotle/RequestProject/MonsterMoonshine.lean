import Mathlib

/-!
# JMD "Full Stack Architecture" — Monstrous-Moonshine numerology

This file formalises the genuine, self-contained *arithmetic* claims in the
source document (the "JMD - Full Stack Architecture" conversation) about
Monstrous Moonshine, the Monster group `M`, and the FRACTRAN/CRT "Monster
machine" coordinates.  The document is overwhelmingly informal, so — exactly as
the bundled prior closure files do for their material — we extract its crisp,
checkable numerical statements and prove them as clean Lean theorems.

Contents:

* **The 15 supersingular primes.** The document's "prime skeleton of the
  Monster": `{2,3,5,7,11,13,17,19,23,29,31,41,47,59,71}`, all prime, exactly
  `15` of them (`card_supersingularPrimes`, `supersingularPrimes_prime`).
* **The Monster order.** `|M| = 2⁴⁶·3²⁰·5⁹·7⁶·11²·13³·17·19·23·29·31·41·47·59·71`,
  and its set of prime divisors is *exactly* the 15 supersingular primes
  (`monster_primeFactors_eq_supersingular`).  This is the precise form of the
  document's "the supersingular primes are the primes dividing `|M|`".
* **The smallest non-trivial irrep dimension.** `196883 = 47·59·71` (the
  product of the three largest supersingular primes), and the first moonshine
  relation `c(1) = 196884 = 196883 + 1` between the `q`-coefficient of `j` and
  the Monster representation dimensions (`dim_smallest_irrep`,
  `moonshine_first_coefficient`).
* **The CRT "Monster machine" period.** `CRT(43,53,54)`: the moduli are
  pairwise coprime, so `ℤ/123066 ≅ ℤ/43 × ℤ/53 × ℤ/54`
  (`crt_period_iso`, `crt_period`).
-/

namespace MonsterMoonshine

open scoped BigOperators

/-! ## The 15 supersingular primes -/

/-- The 15 **supersingular primes** — the prime skeleton of the Monster `M`. -/
def supersingularPrimes : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71}

/-- There are exactly **15** supersingular primes. -/
theorem card_supersingularPrimes : supersingularPrimes.card = 15 := by
  decide

/-- Every supersingular prime is indeed prime. -/
theorem supersingularPrimes_prime :
    ∀ p ∈ supersingularPrimes, Nat.Prime p := by
  decide

/-! ## The Monster order and its prime skeleton -/

/-- The order of the Monster group
`|M| = 2⁴⁶·3²⁰·5⁹·7⁶·11²·13³·17·19·23·29·31·41·47·59·71`. -/
def monsterOrder : ℕ :=
  2 ^ 46 * 3 ^ 20 * 5 ^ 9 * 7 ^ 6 * 11 ^ 2 * 13 ^ 3 * 17 * 19 * 23 * 29 * 31 *
    41 * 47 * 59 * 71

/-
**The Monster's prime skeleton.** The set of primes dividing `|M|` is
*exactly* the 15 supersingular primes.
-/
theorem monster_primeFactors_eq_supersingular :
    monsterOrder.primeFactors = supersingularPrimes := by
  native_decide

/-! ## The smallest non-trivial irreducible representation -/

/-- **`196883 = 47·59·71`** — the dimension of the smallest non-trivial
irreducible representation of `M` is the product of the three largest
supersingular primes. -/
theorem dim_smallest_irrep : (196883 : ℕ) = 47 * 59 * 71 := by
  norm_num

/-- **First moonshine coefficient.** The `q`-coefficient of the modular
`j`-invariant is `c(1) = 196884 = 196883 + 1 = 1 + dim ρ₁`, the sum of the two
smallest irreducible character dimensions of `M`. -/
theorem moonshine_first_coefficient : (196884 : ℕ) = 196883 + 1 := by
  norm_num

/-! ## The CRT "Monster machine" period `CRT(43, 53, 54)` -/

/-- The three moduli of the document's `CRT54,53,43` machine are pairwise
coprime. -/
theorem crt_moduli_coprime :
    Nat.Coprime 43 53 ∧ Nat.Coprime 43 54 ∧ Nat.Coprime 53 54 := by
  decide

/-
**CRT period decomposition.** Because `43, 53, 54` are pairwise coprime, the
cyclic clock of period `43·53·54 = 123066` factors as the product of the three
individual clocks: `ℤ/123066 ≅ ℤ/43 × ℤ/53 × ℤ/54`.
-/
noncomputable def crt_period_iso :
    ZMod (43 * 53 * 54) ≃+* ZMod 43 × (ZMod 53 × ZMod 54) :=
  (ZMod.chineseRemainder (show Nat.Coprime 43 (53 * 54) by decide)).trans
    (RingEquiv.prodCongr (RingEquiv.refl (ZMod 43))
      (ZMod.chineseRemainder (show Nat.Coprime 53 54 by decide)))

/-- The total period of the `CRT(43,53,54)` machine is `123066`. -/
theorem crt_period : 43 * 53 * 54 = 123066 := by
  norm_num

end MonsterMoonshine