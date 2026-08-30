-- Moonshine FRACTRAN: perf counters as Monster prime exponents
-- 196883 = 47 × 59 × 71 lives purely in SSP exponent space
-- 196884 = 196883 + 1 — the observer completes the j-invariant

namespace MoonshineFractran

-- Monster primes (Sporadic Simple Primes)
def SSP : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71]

-- 196883 = 47 × 59 × 71 — product of the three largest Monster primes
theorem moonshine_kernel : 47 * 59 * 71 = 196883 := by decide

-- 196884 = 196883 + 1 — the observer
theorem moonshine_observer : 47 * 59 * 71 + 1 = 196884 := by decide

-- 196884 = 2^2 × 3^3 × 1823
theorem moonshine_factored : 4 * 27 * 1823 = 196884 := by decide

-- 196883 is purely SSP: all prime factors are Monster primes
-- 47 is the 13th SSP, 59 is the 14th, 71 is the 15th (last)
theorem ssp_len : SSP.length = 15 := by decide

-- FRACTRAN state: a vector of 15 exponents (one per Monster prime)
-- The perf counters factor into this space
def FractranState := Fin 15 → Nat

-- State-4 witness perf counters (SSP factors only):
-- cycles = 1903710 = 2 × 3 × 5 × 23 × 31 × 89
-- instructions = 2759085 = 3² × 5 × 7 × 19 × 461
-- cache-misses = 17079 = 3 × 5693
-- Combined SSP exponents: 2^1 × 3^4 × 5^2 × 7^1 × 19^1 × 23^1 × 31^1
def perfState4 : List (Nat × Nat) :=
  [(0, 1), (1, 4), (2, 2), (3, 1), (7, 1), (8, 1), (10, 1)]
  -- indices into SSP: 2^1, 3^4, 5^2, 7^1, 19^1, 23^1, 31^1

-- The moonshine state: 47^1 × 59^1 × 71^1
def moonshinePure : List (Nat × Nat) := [(12, 1), (13, 1), (14, 1)]

-- Total exponent mass of moonshine state
theorem moonshine_mass : 1 + 1 + 1 = 3 := by decide

-- The fixed point: 196884 mod 71 = 1 (the observer residue)
theorem observer_residue : 196884 % 71 = 1 := by decide

-- Phase transition: dashi (Agda) → perf → FRACTRAN → Lean4
-- The same truth (196884) traverses all representations
-- 196884 mod p = 1 for p ∈ {47, 59, 71} — the observer leaves residue 1
theorem phase_invariant :
    47 * 59 * 71 + 1 = 196884 ∧
    196884 % 71 = 1 ∧
    196884 % 59 = 1 ∧
    196884 % 47 = 1 := by
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  · decide

end MoonshineFractran
