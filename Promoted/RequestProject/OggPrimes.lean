import Mathlib

/-!
# OggPrimes — the supersingular (Ogg) primes of Monstrous Moonshine

The **supersingular primes** are the 15 primes that divide the order of the
Monster simple group `𝕄`.  By a theorem of Ogg, they are exactly the primes
`p` for which the modular curve `X₀(p)⁺` (the quotient of `X₀(p)` by the
Fricke/Atkin–Lehner involution) has genus zero:

  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71.

Ogg famously offered a bottle of Jack Daniel's for an explanation of the
coincidence between this list and the prime divisors of `|𝕄|` — a coincidence
that became one of the founding observations of Monstrous Moonshine.

This module collects the list and its elementary properties so downstream
modules (e.g. `RequestProject.CRTTorus`) can refer to `OggPrimes.supersingularPrimes`.
-/

namespace OggPrimes

/-- The 15 supersingular (Ogg) primes dividing `|𝕄|` (OEIS A002267). -/
def supersingularPrimes : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

/-- There are exactly 15 supersingular primes. -/
theorem supersingularPrimes_length : supersingularPrimes.length = 15 := by decide

/-- Every supersingular prime is in fact prime. -/
theorem supersingularPrimes_prime :
    ∀ p ∈ supersingularPrimes, Nat.Prime p := by decide

/-- The supersingular primes list has no duplicates. -/
theorem supersingularPrimes_nodup : supersingularPrimes.Nodup := by decide

/-- The three largest supersingular primes are the CRT-torus radii `47, 59, 71`. -/
theorem largest_three :
    47 ∈ supersingularPrimes ∧ 59 ∈ supersingularPrimes ∧ 71 ∈ supersingularPrimes := by
  decide

/-- `71` is the largest supersingular prime. -/
theorem max_is_71 : ∀ p ∈ supersingularPrimes, p ≤ 71 := by decide

end OggPrimes
